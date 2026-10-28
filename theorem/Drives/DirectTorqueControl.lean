import dependencies.Mathlib
import theorem.Transform.SpaceVector
import theorem.Drives.InductionMachine
import theorem.Drives.PMSM

/-! # Direct torque control: flux estimation, load-angle torque, switching geometry

Static foundation for direct torque control: the voltage-model flux estimate, the load-angle
torque formulas and the geometry of the switching table.  No closed-loop claim is made.

Model boundary.
* Symmetric three-phase machine, complex space vectors in the stationary αβ frame, motor
  convention, amplitude-invariant transform, `np` = number of **pole pairs**. Stator voltage
  equation `dψ_s/dt = v_s − r_s i_s`. Induction-machine flux relations as in
  `theorem/Drives/InductionMachine.lean`; PMSM in the rotor frame as in
  `theorem/Drives/PMSM.lean`.
* Excluded: the DTC hysteresis loops (not formalized), PWM and sampling.

Source: work-sync `theory/T-direct-torque-control.md` §1.1–§1.6.

Results.
* `fluxVoltageModel`: `ψ_s(t) = ψ_s(0) + ∫₀ᵗ (v_s − r_s i_s)` (needs only `r_s`).
* `normSq_flux_hasDerivAt`: `d|ψ_s|²/dt = 2 Re(conj ψ_s · (v_s − r_s i_s))` — only the radial
  component of the applied voltage changes the flux magnitude.
* `torque_loadAngle_IM`: `T_e = (3/2) np (L_m/(σ L_s L_r)) |ψ_s||ψ_r| sin(θ_s − θ_r)`, with the
  load angle `δ_sr = θ_s − θ_r` (stator flux leading the rotor flux is motoring); `cross_polar`
  is the polar cross-product identity behind it.
* `torque_loadAngle_PMSM`: `T_e = (3/2) np (ψ_f |ψ_s| sin δ / L_d + |ψ_s|² (L_d − L_q) sin 2δ /
  (2 L_d L_q))`, `δ` the stator-flux angle in the rotor frame (the note's "reluctance term"
  made explicit).
* `radial_tangential`: components of `v_k = (2/3)V_dc e^{jα}` along / across the flux
  direction `e^{jθ}` are `(2/3)V_dc cos(α − θ)` and `(2/3)V_dc sin(α − θ)`.
* `sector_signs`, `sector_boundary_radial_zero`: geometric basis of the Takahashi–Noguchi
  table. With the flux at relative angle `φ ∈ [−π/6, π/6]` from the centre of sector `k`:
  `v_{k+1}` has radial `≥ 0`, tangential `> 0`; `v_{k+2}` radial `≤ 0`, tangential `> 0`;
  `v_{k−1}` radial `≥ 0`, tangential `< 0`; `v_{k−2}` radial `≤ 0`, tangential `< 0`; the
  radial component of `v_{k+1}` vanishes exactly at the lower boundary `φ = −π/6` and that of
  `v_{k+2}` exactly at the upper boundary `φ = π/6`.

Correction (§1.2).
* With `p` = pole pairs the torque is `T_e = (3/2) p Im{conj ψ_s · i_s}`
  (`Transform.SpaceVector.torque`, `Transform.SpaceVector.torque_coefficient_unique`), not
  `(3/2)(p/2)…`.
-/

noncomputable section
namespace powerlib.Drives.DTC

open Complex ComplexConjugate
open powerlib.Transform.SpaceVector

/-- Voltage-model stator flux estimate (integral form of `ψ̇ = v − r i`). -/
@[tmio T, powerlib_foundation] theorem fluxVoltageModel (r : ℝ) (v i ψ : ℝ → ℂ) (hv : Continuous v)
    (hi : Continuous i) (hψ : ∀ t, HasDerivAt ψ (v t - r * i t) t) (t : ℝ) :
    ψ t = ψ 0 + ∫ τ in (0 : ℝ)..t, (v τ - r * i τ) := by
  have hc : Continuous fun τ => v τ - r * i τ := hv.sub (continuous_const.mul hi)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hψ τ)
    (hc.intervalIntegrable 0 t)]
  ring

/-- `d|ψ|²/dt = 2 Re(conj ψ · ψ̇)`. -/
@[powerlib_foundation] theorem normSq_flux_hasDerivAt (ψ : ℝ → ℂ) (dψ : ℂ) (t : ℝ)
    (h : HasDerivAt ψ dψ t) :
    HasDerivAt (fun s => Complex.normSq (ψ s)) (2 * (conj (ψ t) * dψ).re) t := by
  have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h)
  have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_def] at hre him
  have := (hre.mul hre).add (him.mul him)
  convert this using 1
  · funext s; simp [Complex.normSq_apply]
  · simp [Complex.mul_re]; ring

/-- `Im(conj(ρ_r e^{jθ_r}) · ρ_s e^{jθ_s}) = ρ_s ρ_r sin(θ_s − θ_r)`. -/
@[tmio T, powerlib_foundation] theorem cross_polar (ρs θs ρr θr : ℝ) :
    (conj (⟨ρr * Real.cos θr, ρr * Real.sin θr⟩ : ℂ) *
        ⟨ρs * Real.cos θs, ρs * Real.sin θs⟩).im = ρs * ρr * Real.sin (θs - θr) := by
  rw [cross_eq, Real.sin_sub]
  ring

/-- **Load-angle torque of the induction machine.** With
`ψ_s = |ψ_s| e^{jθ_s}`, `ψ_r = |ψ_r| e^{jθ_r}`:
`T_e = (3/2) np (L_m/(σ L_s L_r)) |ψ_s| |ψ_r| sin(θ_s − θ_r)`. -/
@[powerlib_foundation] theorem torque_loadAngle_IM (p : InductionMachine.Params) (hLr : p.Lr ≠ 0)
    (hσ : p.sigma * p.Ls ≠ 0) (np : ℝ) (is ir : ℂ) (ρs θs ρr θr : ℝ)
    (hs : InductionMachine.statorFlux p is ir = ⟨ρs * Real.cos θs, ρs * Real.sin θs⟩)
    (hr : InductionMachine.rotorFlux p is ir = ⟨ρr * Real.cos θr, ρr * Real.sin θr⟩) :
    torque np (InductionMachine.statorFlux p is ir) is =
      3 / 2 * np * (p.Lm / (p.sigma * p.Ls * p.Lr)) * ρs * ρr * Real.sin (θs - θr) := by
  have hi := InductionMachine.statorCurrent_of_fluxes p hLr hσ is ir
  set ψs := InductionMachine.statorFlux p is ir
  set ψr := InductionMachine.rotorFlux p is ir
  unfold torque
  rw [hi]
  have hσ' : ((p.sigma * p.Ls : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ
  have key : (conj ψs * ((ψs - ((p.Lm / p.Lr : ℝ) : ℂ) * ψr) / ((p.sigma * p.Ls : ℝ) : ℂ))).im =
      p.Lm / (p.sigma * p.Ls * p.Lr) * (conj ψr * ψs).im := by
    rw [cross_eq, cross_eq]
    simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  rw [key, hs, hr, cross_polar]
  ring

/-- **Load-angle torque of the PMSM** (rotor frame): if the stator flux
`ψ_s = (L_d i_d + ψ_f) + j L_q i_q` equals `ρ e^{jδ}`, then
`T_e = (3/2) np (ψ_f ρ sin δ / L_d + ρ² (L_d − L_q) sin 2δ / (2 L_d L_q))`. -/
@[powerlib_foundation] theorem torque_loadAngle_PMSM (np ψf Ld Lq id iq ρ δ : ℝ) (hd : Ld ≠ 0)
    (hq : Lq ≠ 0) (h1 : Ld * id + ψf = ρ * Real.cos δ) (h2 : Lq * iq = ρ * Real.sin δ) :
    PMSM.torque np ψf Ld Lq id iq =
      3 / 2 * np * (ψf * ρ * Real.sin δ / Ld +
        ρ ^ 2 * (Ld - Lq) * Real.sin (2 * δ) / (2 * Ld * Lq)) := by
  have hid : id = (ρ * Real.cos δ - ψf) / Ld := by field_simp; linarith
  have hiq : iq = ρ * Real.sin δ / Lq := by field_simp; linarith
  rw [PMSM.torque, hid, hiq, Real.sin_two_mul]
  field_simp
  ring

/-! ## Switching-table geometry -/

/-- Radial and tangential components of `r e^{jα}` with respect to the direction `e^{jθ}`. -/
@[powerlib_foundation] theorem radial_tangential (r α θ : ℝ) :
    ((⟨r * Real.cos α, r * Real.sin α⟩ : ℂ) * conj ⟨Real.cos θ, Real.sin θ⟩).re =
        r * Real.cos (α - θ) ∧
      ((⟨r * Real.cos α, r * Real.sin α⟩ : ℂ) * conj ⟨Real.cos θ, Real.sin θ⟩).im =
        r * Real.sin (α - θ) := by
  constructor
  · simp [Complex.mul_re, Real.cos_sub]; ring
  · simp [Complex.mul_im, Real.sin_sub]; ring

/-- Sign pattern of the radial (`cos`) and tangential (`sin`) components of the vectors
`v_{k+1}, v_{k+2}, v_{k−1}, v_{k−2}` (relative angles `±π/3, ±2π/3`) for a flux inside the
sector, `φ ∈ [−π/6, π/6]`. -/
@[powerlib_foundation] theorem sector_signs (φ : ℝ)
    (hφ : φ ∈ Set.Icc (-(Real.pi / 6)) (Real.pi / 6)) :
    (0 ≤ Real.cos (Real.pi / 3 - φ) ∧ 0 < Real.sin (Real.pi / 3 - φ)) ∧
      (Real.cos (2 * Real.pi / 3 - φ) ≤ 0 ∧ 0 < Real.sin (2 * Real.pi / 3 - φ)) ∧
      (0 ≤ Real.cos (-(Real.pi / 3) - φ) ∧ Real.sin (-(Real.pi / 3) - φ) < 0) ∧
      (Real.cos (-(2 * Real.pi / 3) - φ) ≤ 0 ∧ Real.sin (-(2 * Real.pi / 3) - φ) < 0) := by
  obtain ⟨h1, h2⟩ := hφ
  have hpi := Real.pi_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply Real.cos_nonneg_of_mem_Icc; constructor <;> linarith
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  · apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> linarith
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  · apply Real.cos_nonneg_of_mem_Icc; constructor <;> linarith
  · apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith
  · rw [show -(2 * Real.pi / 3) - φ = -(2 * Real.pi / 3 + φ) by ring, Real.cos_neg]
    apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> linarith
  · apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith

/-- The radial component of `v_{k+1}` vanishes exactly at the lower sector boundary and that
of `v_{k+2}` exactly at the upper boundary (the reason the sectors are centred on the
active vectors). -/
@[powerlib_foundation] theorem sector_boundary_radial_zero (φ : ℝ)
    (hφ : φ ∈ Set.Icc (-(Real.pi / 6)) (Real.pi / 6)) :
    (Real.cos (Real.pi / 3 - φ) = 0 ↔ φ = -(Real.pi / 6)) ∧
      (Real.cos (2 * Real.pi / 3 - φ) = 0 ↔ φ = Real.pi / 6) := by
  obtain ⟨h1, h2⟩ := hφ
  have hpi := Real.pi_pos
  have key : ∀ x, x ∈ Set.Icc 0 Real.pi → (Real.cos x = 0 ↔ x = Real.pi / 2) := by
    intro x hx
    constructor
    · intro h
      exact Real.injOn_cos hx ⟨by linarith, by linarith⟩ (by rw [h, Real.cos_pi_div_two])
    · intro h; rw [h, Real.cos_pi_div_two]
  constructor
  · rw [key _ ⟨by linarith, by linarith⟩]
    constructor <;> intro h <;> linarith
  · rw [key _ ⟨by linarith, by linarith⟩]
    constructor <;> intro h <;> linarith

end powerlib.Drives.DTC
