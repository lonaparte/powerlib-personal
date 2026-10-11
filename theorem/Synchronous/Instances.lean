import theorem.Synchronous.Swing
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Instances of the canonical swing model: VSG on an infinite bus, classical SMIB,
post-fault SMIB with line resistance

All three are instances of `SwingParams` (`theorem/Synchronous/Swing.lean`); the state is
`(δ, ω)` with `ω` the angular-frequency deviation in rad/s, continuous time, constant
mechanical / reference power, no PLL, delay, PWM, current limiting, excitation or governor
dynamics, ideal infinite bus.

* `VSGInfiniteBus`: VSG / VSM with virtual inertia constant `H` (s), per-unit damping `D_p`,
  reference power `P_ref`, internal EMF `E`, grid voltage `V_g`, grid reactance `X_g`, nominal
  frequency `ω_s`, on a lossless line.  Export-positive power (GFM family exception,
  T-gfm-control §1.0).  The per-unit swing `2H ω̇_pu = P_ref − P − D_p ω_pu` is written with
  the frequency deviation in rad/s, `ω = ω_s ω_pu`, so `M = 2H/ω_s`, `D = D_p/ω_s`,
  `P = (E V_g / X_g) sin δ`.
* `ClassicalSMIB`: classical synchronous machine model (`E'` behind `X_d'`, constant `P_m`,
  generator OUT-positive stator convention, T-sync-machine §1.9).
* `PostFaultSMIB`: SMIB through a Thevenin impedance `Z_e = R_e + j X_e` with resistance; the
  power-angle curve `P_e = G_e E'² + (E' V_g / |Z_e|) sin(δ − α)` is derived from the complex
  power `S̄ = Ē' Ī*` (generator OUT-positive, T-transient-stability §1.2).

Corrections.
* T-vsg-control §1.10 writes `Δθ̇ = Δω`, `2H Δω̇ = −K_E Δθ − D_p Δω` with `Δω` in per unit and
  `Δθ` in rad, which drops the factor `ω_s`.  The correct characteristic polynomial is
  `2H s² + D_p s + ω_s K_E`, so `ω_n² = ω_s K_E / (2H)` and `ζ = D_p / (2 √(2H ω_s K_E))`;
  with the note's data (`H = 2 s`, `K_E = 8`, `ω_s = 2π·50`) `ω_n ≈ 25.07 rad/s`, not
  `1.41 rad/s` (`vsg_naturalFrequency_numeric`).

Source: work-sync theory/T-vsg-control.md §1.1, §1.2, §1.10; theory/T-sync-machine.md §1.9;
theory/T-transient-stability.md §1.2, §1.4;
projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md §1, §3.
-/

noncomputable section
namespace powerlib.Synchronous
open Set Matrix
open powerlib.Dynamics (State)

/-! ## VSG on an infinite bus -/

/-- Parameters of a VSG connected to an infinite bus through a lossless reactance. -/
structure VSGInfiniteBus where
  H : ℝ
  ωs : ℝ
  Dp : ℝ
  Pref : ℝ
  E : ℝ
  Vg : ℝ
  Xg : ℝ

namespace VSGInfiniteBus

variable (v : VSGInfiniteBus)

/-- Maximum transferable power `E V_g / X_g`. -/
def Pmax : ℝ := v.E * v.Vg / v.Xg

/-- The VSG closed loop as a swing model: `M = 2H/ω_s`, `D = D_p/ω_s`,
`P_e(δ) = (E V_g / X_g) sin δ`. -/
def toSwing : SwingParams := ⟨2 * v.H / v.ωs, v.Dp / v.ωs, v.Pref, 0, v.Pmax, 0⟩

/-- Synchronizing coefficient `K_E = (E V_g / X_g) cos δ₀`. -/
def KE (δ₀ : ℝ) : ℝ := v.Pmax * Real.cos δ₀

/-- Positivity of the physical parameters. -/
structure Pos : Prop where
  H : 0 < v.H
  ωs : 0 < v.ωs
  E : 0 < v.E
  Vg : 0 < v.Vg
  Xg : 0 < v.Xg

variable {v}

@[powerlib_foundation] theorem Pos.M (h : v.Pos) : 0 < v.toSwing.M :=
  show 0 < 2 * v.H / v.ωs from div_pos (mul_pos two_pos h.H) h.ωs

@[powerlib_foundation] theorem Pos.Pmax (h : v.Pos) : 0 < v.Pmax :=
  show 0 < v.E * v.Vg / v.Xg from div_pos (mul_pos h.E h.Vg) h.Xg

variable (v)

/-- Equilibria of the VSG on an infinite bus exist iff `|P_ref| ≤ E V_g / X_g`. -/
@[powerlib_domain] theorem exists_equilibrium_iff (h : v.Pos) :
    (∃ x, v.toSwing.field x = 0) ↔ |v.Pref| ≤ v.Pmax := by
  have := v.toSwing.exists_equilibrium_iff h.M.ne' h.Pmax
  simpa [toSwing] using this

/-- The loading angle `δ₀ = arcsin(P_ref X_g / (E V_g))` is locally exponentially stable
(`D_p > 0`, `|P_ref| < E V_g / X_g`). -/
@[powerlib_domain] theorem locallyExponentiallyStable (h : v.Pos) (hD : 0 < v.Dp)
    (hP : |v.Pref| < v.Pmax) :
    Dynamics.LocallyExponentiallyStable v.toSwing.field
      (mkState (Real.arcsin (v.Pref / v.Pmax)) 0) := by
  have hD' : 0 < v.toSwing.D := show 0 < v.Dp / v.ωs from div_pos hD h.ωs
  have hP' : |v.toSwing.Pm - v.toSwing.k₁| < v.toSwing.k₂ := by simpa [toSwing] using hP
  have := v.toSwing.locallyExponentiallyStable_deltaS h.M hD' h.Pmax hP'
  simpa [SwingParams.deltaS, SwingParams.loadRatio, toSwing] using this

/-- The second equilibrium `π − δ₀` is unstable for every damping. -/
@[powerlib_domain] theorem unstable (h : v.Pos) (hP : |v.Pref| < v.Pmax) :
    Dynamics.Unstable v.toSwing.field
      (mkState (Real.pi - Real.arcsin (v.Pref / v.Pmax)) 0) := by
  have := v.toSwing.unstable_deltaU h.M h.Pmax (by simpa [toSwing] using hP)
  simpa [SwingParams.deltaU, SwingParams.loadRatio, toSwing] using this

/-- Without damping (`D_p = 0`) — and for any `D_p ≥ 0` — the loading angle is Lyapunov
stable (energy function). -/
@[powerlib_domain] theorem lyapunovStable (h : v.Pos) (hD : 0 ≤ v.Dp)
    (hP : |v.Pref| < v.Pmax) :
    Dynamics.LyapunovStable v.toSwing.field (mkState (Real.arcsin (v.Pref / v.Pmax)) 0) := by
  have hD' : 0 ≤ v.toSwing.D := show 0 ≤ v.Dp / v.ωs from div_nonneg hD h.ωs.le
  have hP' : |v.toSwing.Pm - v.toSwing.k₁| < v.toSwing.k₂ := by simpa [toSwing] using hP
  have := v.toSwing.lyapunovStable_deltaS h.M hD' h.Pmax hP'
  simpa [SwingParams.deltaS, SwingParams.loadRatio, toSwing] using this

/-- Corrected per-unit characteristic polynomial (T-vsg-control §1.10):
`ω_s · M · det(sI − J) = 2H s² + D_p s + ω_s K_E`. -/
@[powerlib_foundation] theorem characteristic_polynomial (h : v.Pos) (δ₀ : ℝ) (s : ℂ) :
    (v.ωs : ℂ) * ((v.toSwing.M : ℂ) *
        (LTI.characteristicMatrix (v.toSwing.jacobian δ₀) s).det) =
      2 * (v.H : ℂ) * s ^ 2 + (v.Dp : ℂ) * s + (v.ωs : ℂ) * (v.KE δ₀ : ℂ) := by
  rw [v.toSwing.characteristic_polynomial h.M.ne']
  have hω : (v.ωs : ℂ) ≠ 0 := by exact_mod_cast h.ωs.ne'
  simp only [toSwing, SwingParams.syncCoeff, KE, sub_zero]
  push_cast
  field_simp

/-- Linearized VSG: exponentially stable iff `D_p > 0` and `K_E > 0` (all coefficients of
`2H s² + D_p s + ω_s K_E` positive). -/
@[powerlib_domain] theorem linearModel_exponentiallyStable_iff (h : v.Pos) (δ₀ : ℝ) :
    LTI.ExponentiallyStable (v.toSwing.linearModel δ₀) ↔ 0 < v.Dp ∧ 0 < v.KE δ₀ := by
  rw [v.toSwing.linearModel_exponentiallyStable_iff h.M]
  simp only [toSwing, SwingParams.syncCoeff, KE, sub_zero, div_pos_iff_of_pos_right h.ωs]

/-- Natural frequency of the corrected linearization: `ω_n² = ω_s K_E / (2H)` equals
`det J`. -/
@[powerlib_foundation] theorem naturalFrequency_sq (h : v.Pos) (δ₀ : ℝ) :
    (v.toSwing.jacobian δ₀).det = v.ωs * v.KE δ₀ / (2 * v.H) := by
  rw [SwingParams.det_jacobian]
  simp only [toSwing, SwingParams.syncCoeff, KE, sub_zero]
  have := h.H.ne'; have := h.ωs.ne'
  field_simp

/-- Damping ratio of the corrected linearization: `(tr J)² / (4 det J) = ζ²` with
`ζ = D_p / (2 √(2H ω_s K_E))`. -/
@[powerlib_foundation] theorem dampingRatio_sq (h : v.Pos) (δ₀ : ℝ) (hK : 0 < v.KE δ₀) :
    (v.toSwing.jacobian δ₀).trace ^ 2 / (4 * (v.toSwing.jacobian δ₀).det) =
      (v.Dp / (2 * Real.sqrt (2 * v.H * v.ωs * v.KE δ₀))) ^ 2 := by
  rw [SwingParams.trace_jacobian, v.naturalFrequency_sq h, div_pow (v.Dp), mul_pow,
    Real.sq_sqrt (by have := h.H; have := h.ωs; positivity)]
  simp only [toSwing]
  have := h.H.ne'; have := h.ωs.ne'; have := hK.ne'
  field_simp
  ring

/-- With the note's data `H = 2 s`, `K_E = 8 pu/rad`, `ω_s = 100π rad/s`, the corrected
natural frequency `√(ω_s K_E / (2H))` lies in `(25, 25.1) rad/s`. -/
@[powerlib_foundation] theorem naturalFrequency_numeric :
    25 < Real.sqrt (100 * Real.pi * 8 / (2 * 2)) ∧
      Real.sqrt (100 * Real.pi * 8 / (2 * 2)) < 25.1 := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

end VSGInfiniteBus

/-! ## Classical SMIB model -/

/-- Classical synchronous machine (`E'` behind `X_d'`) on an infinite bus `V_∞ ∠ 0`. -/
structure ClassicalSMIB where
  M : ℝ
  D : ℝ
  Pm : ℝ
  E' : ℝ
  Vinf : ℝ
  Xd' : ℝ

namespace ClassicalSMIB

variable (m : ClassicalSMIB)

def Pmax : ℝ := m.E' * m.Vinf / m.Xd'

def toSwing : SwingParams := ⟨m.M, m.D, m.Pm, 0, m.Pmax, 0⟩

/-- An equilibrium with `δ₀ ∈ (−π/2, π/2)` is locally exponentially stable (`M, D > 0`,
`E' V_∞ / X_d' > 0`). -/
@[powerlib_domain] theorem locallyExponentiallyStable (hM : 0 < m.M) (hD : 0 < m.D)
    (hP : 0 < m.Pmax) {δ₀ : ℝ} (hδ : δ₀ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (heq : m.toSwing.field (mkState δ₀ 0) = 0) :
    Dynamics.LocallyExponentiallyStable m.toSwing.field (mkState δ₀ 0) :=
  m.toSwing.locallyExponentiallyStable_of_syncCoeff_pos hM hD heq
    (by simpa [toSwing, SwingParams.syncCoeff] using mul_pos hP (Real.cos_pos_of_mem_Ioo hδ))

/-- An equilibrium with `cos δ₀ < 0` is unstable for every damping. -/
@[powerlib_domain] theorem unstable (hM : 0 < m.M) (hP : 0 < m.Pmax) {δ₀ : ℝ}
    (hδ : Real.cos δ₀ < 0) (heq : m.toSwing.field (mkState δ₀ 0) = 0) :
    Dynamics.Unstable m.toSwing.field (mkState δ₀ 0) :=
  m.toSwing.unstable_of_syncCoeff_neg hM heq
    (by simpa [toSwing, SwingParams.syncCoeff] using mul_neg_of_pos_of_neg hP hδ)

/-- Exact overdamping threshold at the stable equilibrium
(damping-class-dichotomy §3): with `μ = 1 − P_m/P_max ∈ (0, 1]`, all eigenvalues of the
linearization at `δ_s` are real iff `D² ≥ 4 M P_max √(μ (2 − μ))`. -/
@[powerlib_domain] theorem eigenvalues_real_iff (hM : 0 < m.M) :
    (∀ (μ : ℂ) (w : Fin 2 → ℂ), w ≠ 0 →
        (m.toSwing.jacobian m.toSwing.deltaS).map (algebraMap ℝ ℂ) *ᵥ w = μ • w → μ.im = 0) ↔
      4 * m.M * m.Pmax * Real.sqrt ((1 - m.Pm / m.Pmax) * (2 - (1 - m.Pm / m.Pmax))) ≤
        m.D ^ 2 := by
  rw [m.toSwing.eigenvalues_real_iff hM]
  have hK : m.toSwing.syncCoeff m.toSwing.deltaS =
      m.Pmax * Real.sqrt ((1 - m.Pm / m.Pmax) * (2 - (1 - m.Pm / m.Pmax))) := by
    simp only [SwingParams.syncCoeff, SwingParams.deltaS, SwingParams.loadRatio, toSwing,
      sub_zero, add_zero]
    rw [Real.cos_arcsin]
    congr 2
    ring
  rw [hK]
  simp only [toSwing]
  constructor <;> intro h <;> linarith

end ClassicalSMIB

/-! ## Post-fault SMIB with line resistance -/

/-- Electrical power from the complex power `S̄ = Ē' Ī*`, `Ī = (Ē' − V̄_g)/Z_e`
(generator OUT-positive): with `Z_e = R_e + j X_e = r e^{jφ}`,
`P_e = Re S̄ = (R_e/r²) E'² + (E' V_g / r) sin(δ − (θ_g + π/2 − φ))`. -/
@[powerlib_foundation] theorem electricalPower_eq (E V δ θg R X r φ : ℝ) (hr : 0 < r)
    (hR : R = r * Real.cos φ) (hX : X = r * Real.sin φ) :
    ((E : ℂ) * Complex.exp (δ * Complex.I) *
      (starRingEnd ℂ) (((E : ℂ) * Complex.exp (δ * Complex.I) -
        (V : ℂ) * Complex.exp (θg * Complex.I)) / ((R : ℂ) + (X : ℂ) * Complex.I))).re =
      R / r ^ 2 * E ^ 2 + E * V / r * Real.sin (δ - (θg + Real.pi / 2 - φ)) := by
  have hr2 : R ^ 2 + X ^ 2 = r ^ 2 := by
    rw [hR, hX]; nlinarith [Real.sin_sq_add_cos_sq φ]
  have hns : Complex.normSq ((R : ℂ) + (X : ℂ) * Complex.I) = r ^ 2 := by
    rw [Complex.normSq_apply]; simp; nlinarith [hr2]
  have hsc : Real.sin (δ - (θg + Real.pi / 2 - φ)) = -Real.cos (δ - θg + φ) := by
    rw [show δ - (θg + Real.pi / 2 - φ) = (δ - θg + φ) - Real.pi / 2 by ring,
      Real.sin_sub_pi_div_two]
  rw [hsc, Real.cos_add, Real.cos_sub, Real.sin_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.div_re,
    Complex.div_im, hns, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im]
  have hφc : Real.cos φ = R / r := by rw [hR]; field_simp
  have hφs : Real.sin φ = X / r := by rw [hX]; field_simp
  rw [hφc, hφs]
  field_simp
  ring_nf
  linear_combination (E ^ 2 * R) * Real.sin_sq_add_cos_sq δ

/-- Post-fault SMIB through `Z_e = r e^{jφ}` to `V_g ∠ θ_g`, internal EMF `E'`. -/
structure PostFaultSMIB where
  M : ℝ
  D : ℝ
  Pm : ℝ
  E' : ℝ
  Vg : ℝ
  θg : ℝ
  r : ℝ
  φ : ℝ

namespace PostFaultSMIB

variable (m : PostFaultSMIB)

/-- `(k₁, k₂, k₃) = (G_e E'², E' V_g / |Z_e|, θ_g + π/2 − φ)`, `G_e = cos φ / |Z_e|`. -/
def toSwing : SwingParams :=
  ⟨m.M, m.D, m.Pm, Real.cos m.φ / m.r * m.E' ^ 2, m.E' * m.Vg / m.r,
    m.θg + Real.pi / 2 - m.φ⟩

/-- The power-angle curve of the post-fault model is the real part of the complex power. -/
@[powerlib_foundation] theorem Pe_eq_complexPower (hr : 0 < m.r) (δ : ℝ) :
    m.toSwing.Pe δ =
      ((m.E' : ℂ) * Complex.exp (δ * Complex.I) *
        (starRingEnd ℂ) (((m.E' : ℂ) * Complex.exp (δ * Complex.I) -
          (m.Vg : ℂ) * Complex.exp (m.θg * Complex.I)) /
          (((m.r * Real.cos m.φ : ℝ) : ℂ) + ((m.r * Real.sin m.φ : ℝ) : ℂ) * Complex.I))).re := by
  rw [electricalPower_eq m.E' m.Vg δ m.θg _ _ m.r m.φ hr rfl rfl]
  simp only [SwingParams.Pe, toSwing]
  field_simp

/-- Post-fault equilibria `δ_s = arcsin((P_m − k₁)/k₂) + k₃` (locally exponentially stable,
`D > 0`) and `δ_u = π − arcsin(·) + k₃` (unstable), when `|P_m − k₁| < k₂`. -/
@[powerlib_domain] theorem deltaS_stable_deltaU_unstable (hM : 0 < m.M) (hD : 0 < m.D)
    (hk : 0 < m.toSwing.k₂) (h : |m.toSwing.Pm - m.toSwing.k₁| < m.toSwing.k₂) :
    Dynamics.LocallyExponentiallyStable m.toSwing.field (mkState m.toSwing.deltaS 0) ∧
      Dynamics.Unstable m.toSwing.field (mkState m.toSwing.deltaU 0) :=
  ⟨m.toSwing.locallyExponentiallyStable_deltaS hM hD hk h, m.toSwing.unstable_deltaU hM hk h⟩

/-- Undamped post-fault model (`D = 0`): `δ_s` is Lyapunov stable. -/
@[powerlib_domain] theorem deltaS_lyapunovStable (hM : 0 < m.M) (hD : 0 ≤ m.D)
    (hk : 0 < m.toSwing.k₂) (h : |m.toSwing.Pm - m.toSwing.k₁| < m.toSwing.k₂) :
    Dynamics.LyapunovStable m.toSwing.field (mkState m.toSwing.deltaS 0) :=
  m.toSwing.lyapunovStable_deltaS hM hD hk h

end PostFaultSMIB

end powerlib.Synchronous
