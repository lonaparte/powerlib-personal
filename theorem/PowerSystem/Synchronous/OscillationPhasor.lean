import theorem.PowerSystem.Synchronous.Swing

/-! # Phase angle between the oscillation phasors of a generator

The method of IEEE PES TR-110 §3.3 that tells natural from forced oscillations by the angle between
the oscillation phasors of a generator's active power and angular frequency. From the linearized
swing equation the damping ratio of the electromechanical mode is derived, the phasors of every
sinusoidal steady state are computed from the model, the damping ratio is read off exactly from
their magnitudes and the angle between them, and the angle threshold of the report is derived.

Model boundary.
* One generator `i`, linearized swing equation at an operating point (3-8):
  `(2H/ω₀) Δδ̈ + (K_D/ω₀) Δδ̇ = ΔP_m − ΔP_e`, with the electrical power deviation (3-9)
  `ΔP_e = K_s Δδ + K_d Δω` and the per-unit speed deviation `Δω = Δδ̇/ω₀`. `Δδ` is the rotor angle
  deviation (rad), `ΔP_m` the mechanical power deviation (an arbitrary input signal: zero for a
  natural oscillation, a periodic forcing for a forced one). Continuous time.
* Parameters (`Params`): inertia constant `H`, synchronous frequency `ω₀`, mechanical damping
  `K_D`, synchronizing torque coefficient `K_s`, damping torque coefficient `K_d`; `Params.Pos`
  asks `H, ω₀, K_s > 0` (no sign is imposed on `K_d`, `K_D`). The report sets `K_D = 0`; results
  that need it say so.
* `ΔP_e` is a memoryless linear function of `(Δδ, Δω)` with constant coefficients: excitation,
  AVR, PSS and network dynamics enter only through the constants `K_s`, `K_d` at the frequency
  considered; nonlinearity, the multi-machine coupling and measurement (Prony extraction of
  phasors) are excluded.
* Sinusoids are written `Re(X e^{jΩt})` (`sinusoid`): the phasor `X = A e^{jθ}` stands for
  `A cos(Ωt + θ)`. The report's `P_a sin(ωt + φ_p)` convention shifts every phasor by the same
  angle, so the angle between two phasors is the same in both conventions.
* The state matrix of (3-10) is the Jacobian `SwingParams.jacobian` at `δ = 0` of the swing model
  `toSwing` (inertia `M = 2H/ω₀`, total damping `D = (K_d + K_D)/ω₀`, power-angle curve
  `K_s sin δ`), so the damping ratio is the swing model's (`SwingParams.dampingRatio_jacobian`).

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-6)–(3-13)
and Fig. 3-5; §3.1 (intrinsic damping of natural and forced oscillations).

Corrections and sharpenings.
* (3-12) reads `ξ = |ΔP_e| cos φ / (2 √(2H ω₀ |ΔP_e| sin φ))`. Exactly,
  `|P| cos φ = K_d |W|` and `|P| sin φ = K_s |D|`, so
  `ξ = (|P| cos φ / |W|) / (2 √(2H ω₀ |P| sin φ / |D|))` (`dampingRatio_eq_angleDamping`); the
  report's formula is the case of unit phasor magnitudes `|W| = |D| = 1`.
* "`ξ` is proportional to `cos φ`": `ξ` is a positive multiple of `cos φ / √(sin φ)`; it has the
  sign of `cos φ` and is strictly decreasing in `φ` on `(0, π)` (`angleDamping_strictAntiOn`).
* (3-13) with general magnitudes: `κ = 8 H ω₀ ξ₀² |W|² / (|D| |P|)`,
  `sin φ₀ = −κ/2 + √(κ²/4 + 1)`; with `|W| = |D| = 1` this is exactly (3-13)
  (`thresholdAngle_unit`).

Results.
* `swing_iff`, `swing_iff_stateSpace` — (3-8) with (3-9) is (3-10),
  `(2H/ω₀) Δδ̈ + ((K_d + K_D)/ω₀) Δδ̇ + K_s Δδ = ΔP_m`, and its state-space form with the state
  matrix `stateMatrix = toSwing.jacobian 0` (`stateMatrix_eq`).
* `dampingRatio_eq`, `dampingRatio_eq_of_KD` — the damping ratio of (3-10) is
  `ξ = (K_d + K_D)/(2√(2Hω₀K_s))`; with `K_D = 0` this is (3-11).
* `powerPhasor_eq`, `sinusoid_solves`, `phasors_of_solution`, `mechPhasor_eq_zero_iff`,
  `natural_dampingRatio` — every sinusoidal steady state `Δδ = Re(D e^{jΩt})`, `Ω ≠ 0`, of the model
  has `Δω = Re(W e^{jΩt})`, `W = jΩD/ω₀`, `ΔP_e = Re(P e^{jΩt})`, `P = K_s D + K_d W`, and needs the
  mechanical power phasor `F = (K_s − (2H/ω₀)Ω² + jΩ(K_d + K_D)/ω₀) D`; conversely that sinusoid
  solves the model with this input. `P` does not depend on `ΔP_m`: the same relation holds in a
  forced and in a natural oscillation. Unforced (`F = 0`, `D ≠ 0`) exactly when
  `K_d + K_D = 0` and `2HΩ² = ω₀K_s`, i.e. `ξ = 0`.
* `norm_freqPhasor`, `norm_mul_cos_lagAngle`, `norm_mul_sin_lagAngle`, `lagAngle_mem` — with
  `φ = lagAngle W P` the angle by which `P` lags `W`: `|W| = (Ω/ω₀)|D|`, `|P| cos φ = K_d |W|`,
  `|P| sin φ = K_s |D|`, and `0 < φ < π` for `D ≠ 0`, `Ω > 0`.
* `dampingRatio_eq_angle`, `dampingRatio_eq_angleDamping` — exact form of (3-12) (above), with
  `K_D` in general and with `K_D = 0`.
* `angleDamping_strictAntiOn`, `angleDamping_pos_iff`, `angleDamping_eq_zero_iff`,
  `angleDamping_neg_iff` — for `φ ∈ (0, π)`: `ξ(φ)` is strictly decreasing, positive iff
  `φ < π/2`, zero iff `φ = π/2`, negative iff `φ > π/2`.
* `thresholdSin_pos`, `thresholdSin_lt_one`, `thresholdAngle_mem`, `angleDamping_thresholdAngle`,
  `angleDamping_lt_iff`, `thresholdAngle_unit` — the threshold `φ₀ = arcsin(sin φ₀) ∈ (0, π/2)`
  of (3-13) satisfies `ξ(φ₀) = ξ₀` and `ξ(φ) < ξ₀ ↔ φ > φ₀` on `(0, π)`.
* `dampingRatio_lt_iff_lagAngle`, `dampingRatio_eq_zero_iff_lagAngle`,
  `dampingRatio_neg_iff_lagAngle`, `natural_lagAngle` — the criterion on the model (`K_D = 0`):
  at every sinusoidal steady state, forced or natural, `ξ < ξ₀ ↔ φ > φ₀`, `ξ = 0 ↔ φ = π/2`,
  `ξ < 0 ↔ φ > π/2`; a sustained unforced oscillation has `φ = π/2` exactly.
-/

noncomputable section
namespace powerlib.Synchronous.OscillationPhasor
open Complex Set Matrix

/-- Parameters of the linearized swing equation (3-8) of one generator with the electrical power
deviation (3-9). -/
structure Params where
  /-- Inertia constant `H` (s). -/
  H : ℝ
  /-- Synchronous angular frequency `ω₀` (rad/s). -/
  ω₀ : ℝ
  /-- Mechanical damping coefficient `K_D`. -/
  KD : ℝ
  /-- Synchronizing torque coefficient `K_s`. -/
  Ks : ℝ
  /-- Damping torque coefficient `K_d`. -/
  Kd : ℝ

/-- Positive inertia constant, synchronous frequency and synchronizing coefficient. -/
structure Params.Pos (p : Params) : Prop where
  H : 0 < p.H
  ω₀ : 0 < p.ω₀
  Ks : 0 < p.Ks

/-- The real sinusoid `Re(X e^{jΩt})` with phasor `X` and angular frequency `Ω`. -/
def sinusoid (X : ℂ) (Ω t : ℝ) : ℝ := (X * Complex.exp (Ω * t * I)).re

/-- The angle `φ` by which the phasor `P` lags the phasor `W`: `arg (W P̄) ∈ (−π, π]`, so that
`P = (|P|/|W|) e^{−jφ} W` for nonzero phasors. -/
def lagAngle (W P : ℂ) : ℝ := Complex.arg (W * (starRingEnd ℂ) P)

@[tmio T, powerlib_foundation] private theorem hasDerivAt_sinusoid (X : ℂ) (Ω t : ℝ) :
    HasDerivAt (sinusoid X Ω) (sinusoid (Ω * I * X) Ω t) t := by
  have h1 : HasDerivAt (fun s : ℂ => (Ω : ℂ) * s * I) ((Ω : ℂ) * I) (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul (Ω : ℂ)).mul_const I
  have h3 := (h1.cexp).const_mul X
  have hre := h3.real_of_complex
  convert hre using 1
  · rfl
  simp only [sinusoid]
  congr 1
  ring

@[tmio T, powerlib_foundation] private theorem sinusoid_add (X Y : ℂ) (Ω t : ℝ) :
    sinusoid (X + Y) Ω t = sinusoid X Ω t + sinusoid Y Ω t := by
  simp [sinusoid, add_mul]

@[tmio T, powerlib_foundation] private theorem sinusoid_ofReal_mul (r : ℝ) (X : ℂ) (Ω t : ℝ) :
    sinusoid (r * X) Ω t = r * sinusoid X Ω t := by
  simp [sinusoid, mul_assoc]

/-- Two sinusoids of the same nonzero frequency agree at every instant only if their phasors are
equal (evaluate at `t = 0` and `t = π/(2Ω)`). -/
@[tmio T, powerlib_foundation] private theorem phasor_unique {X Y : ℂ} {Ω : ℝ} (hΩ : Ω ≠ 0)
    (h : ∀ t, sinusoid X Ω t = sinusoid Y Ω t) : X = Y := by
  have h0 := h 0
  have h1 := h (Real.pi / 2 / Ω)
  have harg : (Ω : ℂ) * ((Real.pi / 2 / Ω : ℝ) : ℂ) * I = (Real.pi / 2 : ℝ) * I := by
    have : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
    push_cast; field_simp
  simp only [sinusoid] at h0 h1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h0
  rw [harg, Complex.exp_mul_I] at h1
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im] at h1
  apply Complex.ext h0
  linarith

namespace Params
variable (p : Params)

/-- Electrical power deviation (3-9): `ΔP_e = K_s Δδ + K_d Δω`. -/
def Pe (δ ω : ℝ) : ℝ := p.Ks * δ + p.Kd * ω

/-- Inertia coefficient `2H/ω₀` of (3-8). -/
def M : ℝ := 2 * p.H / p.ω₀

/-- Total damping coefficient `(K_d + K_D)/ω₀` of (3-10). -/
def D : ℝ := (p.Kd + p.KD) / p.ω₀

/-- (3-8) with (3-9) at one instant (angle `δ`, its rate `δ'`, its acceleration `δ''`, mechanical
power `P_m`) is (3-10). -/
@[tmio M, powerlib_domain] theorem swing_iff (δ δ' δ'' Pm : ℝ) :
    2 * p.H / p.ω₀ * δ'' + p.KD / p.ω₀ * δ' = Pm - p.Pe δ (δ' / p.ω₀) ↔
      p.M * δ'' + p.D * δ' + p.Ks * δ = Pm := by
  unfold Pe M D
  constructor <;> intro h <;> linear_combination h

/-- The swing model with inertia `M`, total damping `D` and power-angle curve `K_s sin δ`
(`SwingParams`); (3-10) is its linearization at `δ = 0`. -/
def toSwing : SwingParams := ⟨p.M, p.D, 0, 0, p.Ks, 0⟩

/-- State matrix of (3-10) in the state `(Δδ, Δδ̇)`: the Jacobian of `toSwing` at `δ = 0`. -/
def stateMatrix : Matrix (Fin 2) (Fin 2) ℝ := p.toSwing.jacobian 0

@[tmio M, powerlib_domain] theorem stateMatrix_eq :
    p.stateMatrix = !![0, 1; -p.Ks / p.M, -p.D / p.M] := by
  simp [stateMatrix, SwingParams.jacobian, SwingParams.syncCoeff, toSwing]

/-- State-space form of (3-8)–(3-9): `(Δδ̇, Δδ̈) = A (Δδ, Δδ̇) + (0, ΔP_m / M)`. -/
@[tmio M, powerlib_domain] theorem swing_iff_stateSpace (hM : p.M ≠ 0) (δ δ' δ'' Pm : ℝ) :
    2 * p.H / p.ω₀ * δ'' + p.KD / p.ω₀ * δ' = Pm - p.Pe δ (δ' / p.ω₀) ↔
      ![δ', δ''] = p.stateMatrix *ᵥ ![δ, δ'] + ![0, Pm / p.M] := by
  rw [swing_iff, stateMatrix_eq]
  have key : δ'' = -p.Ks / p.M * δ + -p.D / p.M * δ' + Pm / p.M ↔
      p.M * δ'' + p.D * δ' + p.Ks * δ = Pm := by
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; field_simp; linear_combination h
  rw [← key]
  constructor
  · intro h
    ext i
    fin_cases i
    · simp
    · simp [h]; ring
  · intro h
    have h1 := congrFun h 1
    simp at h1
    linear_combination h1

/-- The damping ratio `ξ` of the electromechanical mode: `Criteria.dampingRatio` of the state
matrix. -/
def dampingRatio : ℝ := Criteria.dampingRatio p.stateMatrix

variable {p}

/-- The damping ratio of (3-10): `ξ = (K_d + K_D) / (2 √(2H ω₀ K_s))`
(`SwingParams.dampingRatio_jacobian` at `M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, `K = K_s`). -/
@[tmio M, powerlib_domain] theorem dampingRatio_eq (hp : p.Pos) :
    p.dampingRatio = (p.Kd + p.KD) / (2 * Real.sqrt (2 * p.H * p.ω₀ * p.Ks)) := by
  have hω := hp.ω₀
  have hM : 0 < p.toSwing.M := div_pos (by linarith [hp.H]) hω
  have hK : p.toSwing.syncCoeff 0 = p.Ks := by simp [SwingParams.syncCoeff, toSwing]
  have hs : Real.sqrt (p.toSwing.M * p.toSwing.syncCoeff 0) =
      Real.sqrt (2 * p.H * p.ω₀ * p.Ks) / p.ω₀ := by
    rw [hK, show p.toSwing.M * p.Ks = 2 * p.H * p.ω₀ * p.Ks / p.ω₀ ^ 2 by
        simp only [toSwing, M]; field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hω.le]
  have hpos : 0 < Real.sqrt (2 * p.H * p.ω₀ * p.Ks) :=
    Real.sqrt_pos.mpr (by have := hp.H; have := hp.Ks; positivity)
  rw [dampingRatio, stateMatrix, SwingParams.dampingRatio_jacobian _ hM (hK ▸ hp.Ks), hs]
  simp only [toSwing, D]
  field_simp

/-- (3-11): with `K_D = 0`, `ξ = K_d / (2 √(2H ω₀ K_s))`. -/
@[tmio M, powerlib_domain] theorem dampingRatio_eq_of_KD (hp : p.Pos) (hKD : p.KD = 0) :
    p.dampingRatio = p.Kd / (2 * Real.sqrt (2 * p.H * p.ω₀ * p.Ks)) := by
  rw [dampingRatio_eq hp, hKD, add_zero]

/-! ## Oscillation phasors of a sinusoidal steady state -/

variable (p)

/-- Phasor `W = jΩD/ω₀` of the per-unit speed deviation `Δω = Δδ̇/ω₀`. -/
def freqPhasor (Ω : ℝ) (Dδ : ℂ) : ℂ := ((Ω / p.ω₀ : ℝ) : ℂ) * I * Dδ

/-- Phasor `P = (K_s + jΩK_d/ω₀) D` of the electrical power deviation `ΔP_e`. -/
def powerPhasor (Ω : ℝ) (Dδ : ℂ) : ℂ := ((p.Ks : ℂ) + ((Ω * p.Kd / p.ω₀ : ℝ) : ℂ) * I) * Dδ

/-- Phasor `F = (K_s − MΩ² + jΩD) D` of the mechanical power deviation needed to sustain the
angle phasor `D` at frequency `Ω` (`M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`). -/
def mechPhasor (Ω : ℝ) (Dδ : ℂ) : ℂ := ((p.Ks - p.M * Ω ^ 2 : ℝ) + ((Ω * p.D : ℝ) : ℂ) * I) * Dδ

/-- The power phasor is the memoryless combination `P = K_s D + K_d W` (3-9): it is fixed by the
angle phasor and the frequency alone, whatever the mechanical forcing. -/
@[tmio M, powerlib_domain] theorem powerPhasor_eq (Ω : ℝ) (Dδ : ℂ) :
    p.powerPhasor Ω Dδ = p.Ks * Dδ + p.Kd * p.freqPhasor Ω Dδ := by
  simp only [powerPhasor, freqPhasor]
  push_cast
  ring

/-- The sinusoid `Δδ = Re(D e^{jΩt})` solves the model: `Δδ̇ = ω₀ Re(W e^{jΩt})` (so
`Δω = Re(W e^{jΩt})`), `Δδ̈ = Re(−Ω² D e^{jΩt})`, `ΔP_e = Re(P e^{jΩt})`, and (3-8)–(3-9) hold with
the mechanical power `ΔP_m = Re(F e^{jΩt})`. -/
@[tmio M, powerlib_domain] theorem sinusoid_solves (hω₀ : p.ω₀ ≠ 0) (Ω : ℝ) (Dδ : ℂ) (t : ℝ) :
    HasDerivAt (sinusoid Dδ Ω) (p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω t) t ∧
    HasDerivAt (fun s => p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω s)
      (sinusoid (-((Ω : ℂ) ^ 2) * Dδ) Ω t) t ∧
    p.Pe (sinusoid Dδ Ω t) (sinusoid (p.freqPhasor Ω Dδ) Ω t) =
      sinusoid (p.powerPhasor Ω Dδ) Ω t ∧
    2 * p.H / p.ω₀ * sinusoid (-((Ω : ℂ) ^ 2) * Dδ) Ω t +
        p.KD / p.ω₀ * (p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω t) =
      sinusoid (p.mechPhasor Ω Dδ) Ω t -
        p.Pe (sinusoid Dδ Ω t) (p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω t / p.ω₀) := by
  have hω₀' : (p.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω₀
  have hW : p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω t = sinusoid (Ω * I * Dδ) Ω t := by
    rw [← sinusoid_ofReal_mul]
    congr 1
    simp only [freqPhasor]
    push_cast
    field_simp
  have hW' : (fun s => p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω s) =
      sinusoid (Ω * I * Dδ) Ω := by
    funext s
    rw [← sinusoid_ofReal_mul]
    congr 1
    simp only [freqPhasor]
    push_cast
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hasDerivAt_sinusoid Dδ Ω t
  · rw [hW']
    convert hasDerivAt_sinusoid (Ω * I * Dδ) Ω t using 2
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [powerPhasor_eq, sinusoid_add, Pe, sinusoid_ofReal_mul, sinusoid_ofReal_mul]
  · rw [mul_div_cancel_left₀ _ hω₀, Pe]
    simp only [sinusoid, ← Complex.re_ofReal_mul, ← Complex.add_re, ← Complex.sub_re]
    congr 1
    simp only [mechPhasor, freqPhasor, M, D]
    push_cast
    field_simp
    ring_nf

/-- The phasors of a sinusoidal steady state are derived from the model: if `Δδ = Re(D e^{jΩt})`,
`Ω ≠ 0`, solves (3-8)–(3-9) (`δ'`, `δ''` its derivatives) with a sinusoidal mechanical power
`Re(G e^{jΩt})`, then `Δω = Δδ̇/ω₀ = Re(W e^{jΩt})`, `ΔP_e = Re(P e^{jΩt})` and `G = F`. -/
@[tmio M, powerlib_domain] theorem phasors_of_solution (hω₀ : p.ω₀ ≠ 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    {Dδ G : ℂ} {δ' δ'' : ℝ → ℝ} (hδ' : ∀ t, HasDerivAt (sinusoid Dδ Ω) (δ' t) t)
    (hδ'' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, 2 * p.H / p.ω₀ * δ'' t + p.KD / p.ω₀ * δ' t =
      sinusoid G Ω t - p.Pe (sinusoid Dδ Ω t) (δ' t / p.ω₀)) :
    (∀ t, δ' t / p.ω₀ = sinusoid (p.freqPhasor Ω Dδ) Ω t) ∧
    (∀ t, p.Pe (sinusoid Dδ Ω t) (δ' t / p.ω₀) = sinusoid (p.powerPhasor Ω Dδ) Ω t) ∧
    G = p.mechPhasor Ω Dδ := by
  have h1 : ∀ t, δ' t = p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω t := fun t =>
    (hδ' t).unique (p.sinusoid_solves hω₀ Ω Dδ t).1
  have hδ'fun : δ' = fun s => p.ω₀ * sinusoid (p.freqPhasor Ω Dδ) Ω s := funext h1
  have h2 : ∀ t, δ'' t = sinusoid (-((Ω : ℂ) ^ 2) * Dδ) Ω t := fun t => by
    have := hδ'' t
    rw [hδ'fun] at this
    exact this.unique (p.sinusoid_solves hω₀ Ω Dδ t).2.1
  have hω : ∀ t, δ' t / p.ω₀ = sinusoid (p.freqPhasor Ω Dδ) Ω t := fun t => by
    rw [h1, mul_div_cancel_left₀ _ hω₀]
  refine ⟨hω, fun t => by rw [hω]; exact (p.sinusoid_solves hω₀ Ω Dδ t).2.2.1, ?_⟩
  apply phasor_unique hΩ
  intro t
  have hs := (p.sinusoid_solves hω₀ Ω Dδ t).2.2.2
  have he := heq t
  rw [h2, h1] at he
  linarith

/-- An unforced sinusoidal steady state: `F = 0` with `D ≠ 0`, `Ω ≠ 0` exactly when the total
damping vanishes, `K_d + K_D = 0`, and `Ω` is the undamped natural frequency, `2HΩ² = ω₀K_s`. -/
@[tmio M, powerlib_domain] theorem mechPhasor_eq_zero_iff (hω₀ : p.ω₀ ≠ 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    {Dδ : ℂ} (hD : Dδ ≠ 0) :
    p.mechPhasor Ω Dδ = 0 ↔ p.Kd + p.KD = 0 ∧ 2 * p.H * Ω ^ 2 = p.ω₀ * p.Ks := by
  rw [mechPhasor, mul_eq_zero, or_iff_left hD, Complex.ext_iff]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re,
    Complex.add_im, Complex.mul_im, zero_add, Complex.zero_im, M, D]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : Ω * ((p.Kd + p.KD) / p.ω₀) = 0 := h2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hΩ
      · rcases div_eq_zero_iff.mp h with h | h
        · exact h
        · exact absurd h hω₀
    · field_simp at h1; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · field_simp; linarith
    · rw [h1]; simp

/-- A sustained unforced sinusoidal oscillation of the model (`ΔP_m ≡ 0`, `D ≠ 0`, `Ω ≠ 0`) has
zero damping ratio, `ξ = 0`, and frequency `Ω² = ω₀ K_s / (2H)`. -/
@[tmio M, powerlib_domain] theorem natural_dampingRatio {p : Params} (hp : p.Pos) {Ω : ℝ}
    (hΩ : Ω ≠ 0) {Dδ : ℂ} (hD : Dδ ≠ 0) {δ' δ'' : ℝ → ℝ}
    (hδ' : ∀ t, HasDerivAt (sinusoid Dδ Ω) (δ' t) t) (hδ'' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, 2 * p.H / p.ω₀ * δ'' t + p.KD / p.ω₀ * δ' t =
      0 - p.Pe (sinusoid Dδ Ω t) (δ' t / p.ω₀)) :
    p.dampingRatio = 0 ∧ Ω ^ 2 = p.ω₀ * p.Ks / (2 * p.H) := by
  have hω₀ := hp.ω₀.ne'
  have heq' : ∀ t, 2 * p.H / p.ω₀ * δ'' t + p.KD / p.ω₀ * δ' t =
      sinusoid 0 Ω t - p.Pe (sinusoid Dδ Ω t) (δ' t / p.ω₀) := by
    intro t; rw [heq t]; simp [sinusoid]
  have hF := (p.phasors_of_solution hω₀ hΩ hδ' hδ'' heq').2.2
  obtain ⟨h1, h2⟩ := (p.mechPhasor_eq_zero_iff hω₀ hΩ hD).mp hF.symm
  refine ⟨by rw [dampingRatio_eq hp, h1, zero_div], ?_⟩
  have := hp.H
  field_simp
  linarith

/-! ## The angle between the power and frequency phasors -/

variable {p}

@[tmio M, powerlib_domain] theorem norm_freqPhasor (hp : p.Pos) {Ω : ℝ} (hΩ : 0 < Ω) (Dδ : ℂ) :
    ‖p.freqPhasor Ω Dδ‖ = Ω / p.ω₀ * ‖Dδ‖ := by
  rw [freqPhasor, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (div_pos hΩ hp.ω₀).le]

/-- `W P̄ = K_d Ω²/ω₀² |D|² + j K_s Ω/ω₀ |D|²`. -/
@[tmio M, powerlib_domain] private theorem freq_mul_conj_power (Ω : ℝ) (Dδ : ℂ) :
    p.freqPhasor Ω Dδ * (starRingEnd ℂ) (p.powerPhasor Ω Dδ) =
      ((p.Kd * (Ω / p.ω₀) ^ 2 * Complex.normSq Dδ : ℝ) : ℂ) +
        ((p.Ks * (Ω / p.ω₀) * Complex.normSq Dδ : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
  simp only [freqPhasor, powerPhasor, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply, map_mul, map_add,
    Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, Complex.neg_im] <;>
  ring

/-- `|P| cos φ = K_d |W|` with `φ` the angle by which `P` lags `W`. -/
@[tmio M, powerlib_domain] theorem norm_mul_cos_lagAngle (hp : p.Pos) {Ω : ℝ} (hΩ : 0 < Ω)
    (Dδ : ℂ) :
    ‖p.powerPhasor Ω Dδ‖ * Real.cos (lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ)) =
      p.Kd * ‖p.freqPhasor Ω Dδ‖ := by
  set W := p.freqPhasor Ω Dδ
  set P := p.powerPhasor Ω Dδ
  have h := Complex.norm_mul_cos_arg (W * (starRingEnd ℂ) P)
  have hre : (W * (starRingEnd ℂ) P).re = p.Kd * (Ω / p.ω₀) ^ 2 * Complex.normSq Dδ := by
    rw [freq_mul_conj_power, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.I_re, mul_zero, add_zero]
  rw [norm_mul, Complex.norm_conj, hre] at h
  have hW : ‖W‖ = Ω / p.ω₀ * ‖Dδ‖ := norm_freqPhasor hp hΩ Dδ
  have hn : Complex.normSq Dδ = ‖Dδ‖ ^ 2 := Complex.normSq_eq_norm_sq Dδ
  rcases eq_or_ne Dδ 0 with h0 | h0
  · have : P = 0 := by simp [P, powerPhasor, h0]
    have hW0 : W = 0 := by simp [W, freqPhasor, h0]
    rw [this, hW0]; simp
  · have hWpos : 0 < ‖W‖ := by
      rw [hW]; exact mul_pos (div_pos hΩ hp.ω₀) (norm_pos_iff.mpr h0)
    rw [lagAngle]
    apply mul_left_cancel₀ hWpos.ne'
    rw [hn] at h
    calc ‖W‖ * (‖P‖ * Real.cos (Complex.arg (W * (starRingEnd ℂ) P)))
        = ‖W‖ * ‖P‖ * Real.cos (Complex.arg (W * (starRingEnd ℂ) P)) := by ring
      _ = p.Kd * (Ω / p.ω₀) ^ 2 * ‖Dδ‖ ^ 2 := h
      _ = ‖W‖ * (p.Kd * ‖W‖) := by rw [hW]; ring

/-- `|P| sin φ = K_s |D|`. -/
@[tmio M, powerlib_domain] theorem norm_mul_sin_lagAngle (hp : p.Pos) {Ω : ℝ} (hΩ : 0 < Ω)
    (Dδ : ℂ) :
    ‖p.powerPhasor Ω Dδ‖ * Real.sin (lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ)) =
      p.Ks * ‖Dδ‖ := by
  set W := p.freqPhasor Ω Dδ
  set P := p.powerPhasor Ω Dδ
  have h := Complex.norm_mul_sin_arg (W * (starRingEnd ℂ) P)
  have him : (W * (starRingEnd ℂ) P).im = p.Ks * (Ω / p.ω₀) * Complex.normSq Dδ := by
    rw [freq_mul_conj_power, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul,
      Complex.I_im, mul_one, zero_add]
  rw [norm_mul, Complex.norm_conj, him] at h
  have hW : ‖W‖ = Ω / p.ω₀ * ‖Dδ‖ := norm_freqPhasor hp hΩ Dδ
  have hn : Complex.normSq Dδ = ‖Dδ‖ ^ 2 := Complex.normSq_eq_norm_sq Dδ
  rcases eq_or_ne Dδ 0 with h0 | h0
  · have : P = 0 := by simp [P, powerPhasor, h0]
    rw [this, h0]; simp
  · have hWpos : 0 < ‖W‖ := by
      rw [hW]; exact mul_pos (div_pos hΩ hp.ω₀) (norm_pos_iff.mpr h0)
    rw [lagAngle]
    apply mul_left_cancel₀ hWpos.ne'
    rw [hn] at h
    calc ‖W‖ * (‖P‖ * Real.sin (Complex.arg (W * (starRingEnd ℂ) P)))
        = ‖W‖ * ‖P‖ * Real.sin (Complex.arg (W * (starRingEnd ℂ) P)) := by ring
      _ = p.Ks * (Ω / p.ω₀) * ‖Dδ‖ ^ 2 := h
      _ = ‖W‖ * (p.Ks * ‖Dδ‖) := by rw [hW]; ring

/-- For `D ≠ 0`, `Ω > 0` and `K_s > 0` the power phasor lags the frequency phasor by an angle in
`(0, π)`. -/
@[tmio M, powerlib_domain] theorem lagAngle_mem (hp : p.Pos) {Ω : ℝ} (hΩ : 0 < Ω) {Dδ : ℂ}
    (hD : Dδ ≠ 0) : lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ) ∈ Ioo 0 Real.pi := by
  have him : 0 < (p.freqPhasor Ω Dδ * (starRingEnd ℂ) (p.powerPhasor Ω Dδ)).im := by
    rw [freq_mul_conj_power]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    have := hp.Ks
    have := div_pos hΩ hp.ω₀
    have := Complex.normSq_pos.mpr hD
    positivity
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) fun h => ?_,
    Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')⟩
  have := (Complex.arg_eq_zero_iff.mp h.symm).2
  linarith

/-! ## The damping ratio read from the phasors -/

variable (p) in
/-- The damping ratio read from the phasor magnitudes `|D|, |W|, |P|` and the lag angle `φ`:
`ξ(φ) = (|P| cos φ / |W|) / (2 √(2H ω₀ |P| sin φ / |D|))` (the exact form of (3-12)). -/
def angleDamping (nD nW nP φ : ℝ) : ℝ :=
  (nP * Real.cos φ / nW) / (2 * Real.sqrt (2 * p.H * p.ω₀ * (nP * Real.sin φ / nD)))

/-- Exact (3-12) with mechanical damping: `ξ = (|P| cos φ / |W| + K_D) / (2 √(2Hω₀ |P| sin φ / |D|))`
at every sinusoidal steady state `D ≠ 0`, `Ω > 0`. -/
@[tmio M, powerlib_domain] theorem dampingRatio_eq_angle (hp : p.Pos) {Ω : ℝ} (hΩ : 0 < Ω)
    {Dδ : ℂ} (hD : Dδ ≠ 0) :
    p.dampingRatio =
      (‖p.powerPhasor Ω Dδ‖ *
          Real.cos (lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ)) /
          ‖p.freqPhasor Ω Dδ‖ + p.KD) /
        (2 * Real.sqrt (2 * p.H * p.ω₀ *
          (‖p.powerPhasor Ω Dδ‖ *
            Real.sin (lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ)) / ‖Dδ‖))) := by
  have hWpos : 0 < ‖p.freqPhasor Ω Dδ‖ := by
    rw [norm_freqPhasor hp hΩ]; exact mul_pos (div_pos hΩ hp.ω₀) (norm_pos_iff.mpr hD)
  rw [norm_mul_cos_lagAngle hp hΩ, norm_mul_sin_lagAngle hp hΩ, mul_div_cancel_right₀ _ hWpos.ne',
    mul_div_cancel_right₀ _ (norm_pos_iff.mpr hD).ne', dampingRatio_eq hp]

/-- Exact (3-12), `K_D = 0`: `ξ = angleDamping |D| |W| |P| φ`. -/
@[tmio M, powerlib_domain] theorem dampingRatio_eq_angleDamping (hp : p.Pos) (hKD : p.KD = 0)
    {Ω : ℝ} (hΩ : 0 < Ω) {Dδ : ℂ} (hD : Dδ ≠ 0) :
    p.dampingRatio = p.angleDamping ‖Dδ‖ ‖p.freqPhasor Ω Dδ‖ ‖p.powerPhasor Ω Dδ‖
      (lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ)) := by
  rw [dampingRatio_eq_angle hp hΩ hD, hKD, add_zero, angleDamping]

/-- `cos φ / √(sin φ)` is strictly decreasing on `(0, π)`. -/
@[tmio T, powerlib_foundation] private theorem strictAntiOn_cos_div_sqrt_sin :
    StrictAntiOn (fun φ => Real.cos φ / Real.sqrt (Real.sin φ)) (Ioo 0 Real.pi) := by
  have hsin : ∀ x ∈ Ioo 0 Real.pi, 0 < Real.sin x := fun x hx => Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi)
  · intro x hx
    have := hsin x hx
    exact (Real.continuous_cos.continuousAt.div
      (Real.continuous_sin.sqrt.continuousAt) (Real.sqrt_pos.mpr this).ne').continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hs := hsin x hx
    have hq := Real.sqrt_pos.mpr hs
    have hd : HasDerivAt (fun φ => Real.cos φ / Real.sqrt (Real.sin φ))
        ((-Real.sin x * Real.sqrt (Real.sin x) -
            Real.cos x * (Real.cos x / (2 * Real.sqrt (Real.sin x)))) /
          Real.sqrt (Real.sin x) ^ 2) x :=
      (Real.hasDerivAt_cos x).div ((Real.hasDerivAt_sin x).sqrt hs.ne') hq.ne'
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have h1 : 0 < Real.sin x * Real.sqrt (Real.sin x) := mul_pos hs hq
    have h2 : 0 ≤ Real.cos x * (Real.cos x / (2 * Real.sqrt (Real.sin x))) := by
      rw [← mul_div_assoc]; exact div_nonneg (mul_self_nonneg _) (by positivity)
    linarith

/-- `ξ(φ) = c · cos φ / √(sin φ)` with `c = |P| / (2 |W| √(2Hω₀|P|/|D|)) > 0`. -/
@[tmio M, powerlib_domain] private theorem angleDamping_eq_mul (hp : p.Pos) {nD nW nP : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (φ : ℝ) :
    p.angleDamping nD nW nP φ =
      nP / (2 * nW * Real.sqrt (2 * p.H * p.ω₀ * nP / nD)) *
        (Real.cos φ / Real.sqrt (Real.sin φ)) := by
  have hH := hp.H
  have hω := hp.ω₀
  have hc : 0 < Real.sqrt (2 * p.H * p.ω₀ * nP / nD) := Real.sqrt_pos.mpr (by positivity)
  rw [angleDamping, show 2 * p.H * p.ω₀ * (nP * Real.sin φ / nD) =
      2 * p.H * p.ω₀ * nP / nD * Real.sin φ by ring,
    Real.sqrt_mul (by positivity)]
  rcases eq_or_ne (Real.sqrt (Real.sin φ)) 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

/-- `ξ(φ)` is strictly decreasing in the lag angle on `(0, π)`. -/
@[tmio M, powerlib_domain] theorem angleDamping_strictAntiOn (hp : p.Pos) {nD nW nP : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) :
    StrictAntiOn (p.angleDamping nD nW nP) (Ioo 0 Real.pi) := by
  have hH := hp.H
  have hω := hp.ω₀
  have hc : 0 < nP / (2 * nW * Real.sqrt (2 * p.H * p.ω₀ * nP / nD)) :=
    div_pos hP (mul_pos (by positivity) (Real.sqrt_pos.mpr (by positivity)))
  intro a ha b hb hab
  rw [angleDamping_eq_mul hp hD hW hP, angleDamping_eq_mul hp hD hW hP]
  exact mul_lt_mul_of_pos_left (strictAntiOn_cos_div_sqrt_sin ha hb hab) hc

@[tmio M, powerlib_domain] private theorem angleDamping_pi_div_two (nD nW nP : ℝ) :
    p.angleDamping nD nW nP (Real.pi / 2) = 0 := by
  simp [angleDamping]

@[tmio T, powerlib_foundation] private theorem pi_div_two_mem : Real.pi / 2 ∈ Ioo 0 Real.pi :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

/-- `ξ(φ) > 0 ↔ φ < π/2` on `(0, π)`. -/
@[tmio M, powerlib_domain] theorem angleDamping_pos_iff (hp : p.Pos) {nD nW nP φ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hφ : φ ∈ Ioo 0 Real.pi) :
    0 < p.angleDamping nD nW nP φ ↔ φ < Real.pi / 2 := by
  rw [← angleDamping_pi_div_two (p := p) nD nW nP]
  exact (angleDamping_strictAntiOn hp hD hW hP).lt_iff_gt pi_div_two_mem hφ

/-- `ξ(φ) = 0 ↔ φ = π/2` on `(0, π)`. -/
@[tmio M, powerlib_domain] theorem angleDamping_eq_zero_iff (hp : p.Pos) {nD nW nP φ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hφ : φ ∈ Ioo 0 Real.pi) :
    p.angleDamping nD nW nP φ = 0 ↔ φ = Real.pi / 2 := by
  rw [← angleDamping_pi_div_two (p := p) nD nW nP]
  exact ((angleDamping_strictAntiOn hp hD hW hP).eq_iff_eq hφ pi_div_two_mem).trans eq_comm

/-- `ξ(φ) < 0 ↔ φ > π/2` on `(0, π)`. -/
@[tmio M, powerlib_domain] theorem angleDamping_neg_iff (hp : p.Pos) {nD nW nP φ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hφ : φ ∈ Ioo 0 Real.pi) :
    p.angleDamping nD nW nP φ < 0 ↔ Real.pi / 2 < φ := by
  rw [← angleDamping_pi_div_two (p := p) nD nW nP]
  exact (angleDamping_strictAntiOn hp hD hW hP).lt_iff_gt hφ pi_div_two_mem

/-! ## The angle threshold (3-13) -/

variable (p)

/-- `κ = 8 H ω₀ ξ₀² |W|² / (|D| |P|)`. -/
def kappa (nD nW nP ξ₀ : ℝ) : ℝ := 8 * p.H * p.ω₀ * ξ₀ ^ 2 * nW ^ 2 / (nD * nP)

/-- `sin φ₀ = −κ/2 + √(κ²/4 + 1)`, the positive root of `s² + κ s − 1 = 0`. -/
def thresholdSin (nD nW nP ξ₀ : ℝ) : ℝ :=
  -(p.kappa nD nW nP ξ₀ / 2) + Real.sqrt (p.kappa nD nW nP ξ₀ ^ 2 / 4 + 1)

/-- The angle threshold `φ₀ = arcsin (sin φ₀)` (3-13). -/
def thresholdAngle (nD nW nP ξ₀ : ℝ) : ℝ := Real.arcsin (p.thresholdSin nD nW nP ξ₀)

variable {p}

@[tmio M, powerlib_domain] private theorem kappa_pos (hp : p.Pos) {nD nW nP ξ₀ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hξ : ξ₀ ≠ 0) : 0 < p.kappa nD nW nP ξ₀ := by
  have := hp.H; have := hp.ω₀
  have := pow_pos (abs_pos.mpr hξ) 2
  rw [sq_abs] at this
  unfold kappa; positivity

@[tmio M, powerlib_domain] theorem thresholdSin_pos (hp : p.Pos) {nD nW nP ξ₀ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hξ : ξ₀ ≠ 0) : 0 < p.thresholdSin nD nW nP ξ₀ := by
  have hk := kappa_pos hp hD hW hP hξ
  have h1 : p.kappa nD nW nP ξ₀ / 2 < Real.sqrt (p.kappa nD nW nP ξ₀ ^ 2 / 4 + 1) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  rw [thresholdSin]
  linarith

@[tmio M, powerlib_domain] theorem thresholdSin_lt_one (hp : p.Pos) {nD nW nP ξ₀ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hξ : ξ₀ ≠ 0) : p.thresholdSin nD nW nP ξ₀ < 1 := by
  have hk := kappa_pos hp hD hW hP hξ
  rw [thresholdSin]
  have : Real.sqrt (p.kappa nD nW nP ξ₀ ^ 2 / 4 + 1) < 1 + p.kappa nD nW nP ξ₀ / 2 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  linarith

/-- `sin² φ₀ + κ sin φ₀ = 1`. -/
@[tmio M, powerlib_domain] private theorem thresholdSin_root (nD nW nP ξ₀ : ℝ) :
    p.thresholdSin nD nW nP ξ₀ ^ 2 + p.kappa nD nW nP ξ₀ * p.thresholdSin nD nW nP ξ₀ = 1 := by
  rw [thresholdSin]
  have h := Real.sq_sqrt (show 0 ≤ p.kappa nD nW nP ξ₀ ^ 2 / 4 + 1 by positivity)
  nlinarith

@[tmio M, powerlib_domain] theorem thresholdAngle_mem (hp : p.Pos) {nD nW nP ξ₀ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hξ : ξ₀ ≠ 0) :
    p.thresholdAngle nD nW nP ξ₀ ∈ Ioo 0 (Real.pi / 2) :=
  ⟨Real.arcsin_pos.mpr (thresholdSin_pos hp hD hW hP hξ),
    Real.arcsin_lt_pi_div_two.mpr (thresholdSin_lt_one hp hD hW hP hξ)⟩

/-- At the threshold angle the phasor damping ratio is exactly `ξ₀`. -/
@[tmio M, powerlib_domain] theorem angleDamping_thresholdAngle (hp : p.Pos) {nD nW nP ξ₀ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hξ : 0 < ξ₀) :
    p.angleDamping nD nW nP (p.thresholdAngle nD nW nP ξ₀) = ξ₀ := by
  have hH := hp.H
  have hω := hp.ω₀
  set s := p.thresholdSin nD nW nP ξ₀ with hs
  have hs0 := thresholdSin_pos hp hD hW hP hξ.ne'
  have hs1 := thresholdSin_lt_one hp hD hW hP hξ.ne'
  have hroot := thresholdSin_root (p := p) nD nW nP ξ₀
  rw [← hs] at hs0 hs1 hroot
  have hsin : Real.sin (p.thresholdAngle nD nW nP ξ₀) = s :=
    Real.sin_arcsin (by linarith) hs1.le
  have hcos : Real.cos (p.thresholdAngle nD nW nP ξ₀) = Real.sqrt (1 - s ^ 2) :=
    Real.cos_arcsin s
  have hcos2 : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by nlinarith)
  have hc0 : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hq : 0 < 2 * p.H * p.ω₀ * (nP * s / nD) := by positivity
  have hq2 := Real.sq_sqrt hq.le
  have hqpos := Real.sqrt_pos.mpr hq
  rw [angleDamping, hsin, hcos]
  rw [← sq_eq_sq₀ (by positivity) hξ.le]
  rw [div_pow, div_pow, mul_pow, mul_pow, hcos2, hq2]
  have hk : 1 - s ^ 2 = p.kappa nD nW nP ξ₀ * s := by linarith
  rw [hk, kappa]
  field_simp
  ring

/-- The criterion (3-13): on `(0, π)`, `ξ(φ) < ξ₀ ↔ φ > φ₀`. -/
@[tmio M, powerlib_domain] theorem angleDamping_lt_iff (hp : p.Pos) {nD nW nP ξ₀ φ : ℝ}
    (hD : 0 < nD) (hW : 0 < nW) (hP : 0 < nP) (hξ : 0 < ξ₀) (hφ : φ ∈ Ioo 0 Real.pi) :
    p.angleDamping nD nW nP φ < ξ₀ ↔ p.thresholdAngle nD nW nP ξ₀ < φ := by
  have hmem := thresholdAngle_mem hp hD hW hP hξ.ne'
  have hmem' : p.thresholdAngle nD nW nP ξ₀ ∈ Ioo 0 Real.pi :=
    ⟨hmem.1, hmem.2.trans (by linarith [Real.pi_pos])⟩
  conv_lhs => rw [← angleDamping_thresholdAngle hp hD hW hP hξ]
  exact (angleDamping_strictAntiOn hp hD hW hP).lt_iff_gt hφ hmem'

/-- With unit phasor magnitudes `|W| = |D| = 1` the threshold is exactly the report's (3-13):
`φ₀ = arcsin(−4Hω₀ξ₀²/|P| + √(16H²ω₀²ξ₀⁴/|P|² + 1))`. -/
@[tmio M, powerlib_domain] theorem thresholdAngle_unit (p : Params) (nP ξ₀ : ℝ) :
    p.thresholdAngle 1 1 nP ξ₀ =
      Real.arcsin (-(4 * p.H * p.ω₀ * ξ₀ ^ 2 / nP) +
        Real.sqrt (16 * p.H ^ 2 * p.ω₀ ^ 2 * ξ₀ ^ 4 / nP ^ 2 + 1)) := by
  rw [thresholdAngle, thresholdSin, kappa]
  congr 2
  · ring
  · congr 1; ring

/-! ## The criterion on the model -/

@[tmio M, powerlib_domain] private theorem norm_powerPhasor_pos (hp : p.Pos) {Ω : ℝ} (hΩ : 0 < Ω)
    {Dδ : ℂ} (hD : Dδ ≠ 0) : 0 < ‖p.powerPhasor Ω Dδ‖ := by
  have h := norm_mul_sin_lagAngle hp hΩ Dδ
  have : 0 < p.Ks * ‖Dδ‖ := mul_pos hp.Ks (norm_pos_iff.mpr hD)
  rcases (norm_nonneg (p.powerPhasor Ω Dδ)).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul] at h; linarith
  · exact h0

/-- The phase-angle criterion on the model (`K_D = 0`): at every sinusoidal steady state
(`D ≠ 0`, `Ω > 0`), whether forced or natural, the damping ratio is below `ξ₀ > 0` exactly when
the lag angle exceeds the threshold `φ₀`. -/
@[tmio M, powerlib_domain] theorem dampingRatio_lt_iff_lagAngle (hp : p.Pos) (hKD : p.KD = 0)
    {Ω : ℝ} (hΩ : 0 < Ω) {Dδ : ℂ} (hD : Dδ ≠ 0) {ξ₀ : ℝ} (hξ : 0 < ξ₀) :
    p.dampingRatio < ξ₀ ↔
      p.thresholdAngle ‖Dδ‖ ‖p.freqPhasor Ω Dδ‖ ‖p.powerPhasor Ω Dδ‖ ξ₀ <
        lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ) := by
  have hWpos : 0 < ‖p.freqPhasor Ω Dδ‖ := by
    rw [norm_freqPhasor hp hΩ]; exact mul_pos (div_pos hΩ hp.ω₀) (norm_pos_iff.mpr hD)
  have hPpos := norm_powerPhasor_pos hp hΩ hD
  rw [dampingRatio_eq_angleDamping hp hKD hΩ hD]
  exact angleDamping_lt_iff hp (norm_pos_iff.mpr hD) hWpos hPpos hξ (lagAngle_mem hp hΩ hD)

/-- On the model (`K_D = 0`): `ξ = 0 ↔ φ = π/2`. -/
@[tmio M, powerlib_domain] theorem dampingRatio_eq_zero_iff_lagAngle (hp : p.Pos)
    (hKD : p.KD = 0) {Ω : ℝ} (hΩ : 0 < Ω) {Dδ : ℂ} (hD : Dδ ≠ 0) :
    p.dampingRatio = 0 ↔ lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ) = Real.pi / 2 := by
  have hWpos : 0 < ‖p.freqPhasor Ω Dδ‖ := by
    rw [norm_freqPhasor hp hΩ]; exact mul_pos (div_pos hΩ hp.ω₀) (norm_pos_iff.mpr hD)
  rw [dampingRatio_eq_angleDamping hp hKD hΩ hD]
  exact angleDamping_eq_zero_iff hp (norm_pos_iff.mpr hD) hWpos (norm_powerPhasor_pos hp hΩ hD)
    (lagAngle_mem hp hΩ hD)

/-- On the model (`K_D = 0`): `ξ < 0 ↔ φ > π/2`. -/
@[tmio M, powerlib_domain] theorem dampingRatio_neg_iff_lagAngle (hp : p.Pos)
    (hKD : p.KD = 0) {Ω : ℝ} (hΩ : 0 < Ω) {Dδ : ℂ} (hD : Dδ ≠ 0) :
    p.dampingRatio < 0 ↔ Real.pi / 2 < lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ) := by
  have hWpos : 0 < ‖p.freqPhasor Ω Dδ‖ := by
    rw [norm_freqPhasor hp hΩ]; exact mul_pos (div_pos hΩ hp.ω₀) (norm_pos_iff.mpr hD)
  rw [dampingRatio_eq_angleDamping hp hKD hΩ hD]
  exact angleDamping_neg_iff hp (norm_pos_iff.mpr hD) hWpos (norm_powerPhasor_pos hp hΩ hD)
    (lagAngle_mem hp hΩ hD)

/-- A sustained unforced sinusoidal oscillation of the model (`K_D = 0`, `ΔP_m ≡ 0`, `D ≠ 0`,
`Ω > 0`) has the power phasor lagging the frequency phasor by exactly `π/2`. -/
@[tmio M, powerlib_domain] theorem natural_lagAngle (hp : p.Pos) (hKD : p.KD = 0) {Ω : ℝ}
    (hΩ : 0 < Ω) {Dδ : ℂ} (hD : Dδ ≠ 0) {δ' δ'' : ℝ → ℝ}
    (hδ' : ∀ t, HasDerivAt (sinusoid Dδ Ω) (δ' t) t) (hδ'' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, 2 * p.H / p.ω₀ * δ'' t + p.KD / p.ω₀ * δ' t =
      0 - p.Pe (sinusoid Dδ Ω t) (δ' t / p.ω₀)) :
    lagAngle (p.freqPhasor Ω Dδ) (p.powerPhasor Ω Dδ) = Real.pi / 2 :=
  (dampingRatio_eq_zero_iff_lagAngle hp hKD hΩ hD).mp
    (natural_dampingRatio hp hΩ.ne' hD hδ' hδ'' heq).1

end Params

end powerlib.Synchronous.OscillationPhasor
