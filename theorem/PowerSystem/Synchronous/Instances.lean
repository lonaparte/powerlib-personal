import theorem.PowerSystem.Synchronous.Swing
import theorem.Grid.PowerFlow
import theorem.PowerSystem.Synchronous.PH
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Instances of the canonical swing model: VSG, classical SMIB, post-fault SMIB with resistance

Three engineering models read as instances of `SwingParams`
(`theorem/PowerSystem/Synchronous/Swing.lean`): a VSG on an infinite bus, the classical synchronous
machine on an infinite bus, and a post-fault SMIB with line resistance.

Model boundary.
* Common to all three: state `(δ, ω)` with `ω` the angular-frequency deviation in rad/s,
  continuous time, constant mechanical / reference power, no PLL, delay, PWM, current limiting,
  excitation or governor dynamics, ideal infinite bus.
* `VSGInfiniteBus`: VSG / VSM with virtual inertia constant `H` (s), per-unit damping `D_p`,
  reference power `P_ref`, internal EMF `E`, grid voltage `V_g`, grid reactance `X_g`, nominal
  frequency `ω_s`, on a lossless line.  Export-positive power (GFM family exception,
  T-gfm-control §1.0).  The per-unit swing `2H ω̇_pu = P_ref − P − D_p ω_pu` is written with
  the frequency deviation in rad/s, `ω = ω_s ω_pu`, so `M = 2H/ω_s`, `D = D_p/ω_s`,
  `P = (E V_g / X_g) sin δ`.
* `ClassicalSMIB`: classical synchronous machine model (`E'` behind `X_d'`, constant `P_m`,
  generator OUT-positive stator convention, T-sync-machine §1.9); on its physical range it is the
  port-Hamiltonian classical machine `ClassicalSMParams` with `b = E' V_∞ / X_d'`
  (`ClassicalSMIB.toPH`), and it is the lossless slice `φ = π/2`, `θ_g = 0`, `r = X_d'` of
  `PostFaultSMIB` (`PostFaultSMIB.toSwing_classical`).
* `PostFaultSMIB`: SMIB through a Thevenin impedance `Z_e = R_e + j X_e` with resistance; the
  power-angle curve `P_e = G_e E'² + (E' V_g / |Z_e|) sin(δ − α)` is derived from the complex
  power `S̄ = Ē' Ī*` (generator OUT-positive, T-transient-stability §1.2).

Source: work-sync `theory/T-vsg-control.md` §1.1, §1.2, §1.10; `theory/T-sync-machine.md` §1.9;
`theory/T-transient-stability.md` §1.2, §1.4;
`projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md` §1, §3.

Results (static evidence on the models; foundation).
* `VSGInfiniteBus.exists_equilibrium_iff` — equilibria exist iff `|P_ref| ≤ E V_g / X_g`.
* `VSGInfiniteBus.characteristic_polynomial`, `naturalFrequency_sq`, `dampingRatio_eq` — the
  corrected characteristic polynomial `2H s² + D_p s + ω_s K_E`, natural frequency and damping
  ratio (`Criteria.dampingRatio` of the Jacobian); `K_E` is the swing synchronizing
  coefficient; `naturalFrequency_numeric` — the note's data give `ω_n ≈ 25.07 rad/s`.
* `ClassicalSMIB.eigenvalues_real_iff` — exact overdamping threshold at the stable equilibrium.
* `electricalPower_eq` — the electrical power from the complex power `S̄ = Ē' Ī*`,
  `Ī = (Ē' − V̄_g)/Z_e`; `PostFaultSMIB.Pe_eq_complexPower` — the post-fault power-angle curve is
  its real part.

Family and connection conclusions.
* No new family: each instance is read through the swing family `Synchronous.Swing.family`
  (nonlinear field about a selected angle) or its linearization `Swing.Linearized.family`
  (`theorem/PowerSystem/Synchronous/Swing.lean`), by its swing parameters `toSwing` and the selected
  angle (`VSGInfiniteBus.atLoading` = `arcsin(P_ref X_g / (E V_g))`, `atAntiLoading` = `π −` that
  angle, or a caller-supplied equilibrium angle).
* Connection conclusions: `VSGInfiniteBus.locallyExponentiallyStable`, `unstable`,
  `lyapunovStable` (members of the nonlinear denotations), `VSGInfiniteBus.linearModel_mem_den_iff`
  (a member of the linearized global exponential denotation iff `D_p > 0 ∧ K_E > 0`),
  `ClassicalSMIB.locallyExponentiallyStable`, `unstable`. The post-fault equilibria
  `δ_s = arcsin((P_m − k₁)/k₂) + k₃` and `δ_u = π − arcsin(·) + k₃` (`|P_m − k₁| < k₂`) are read
  at `PostFaultSMIB.toSwing` by `Swing.deltaS_mem_den_locallyExponentiallyStable` (`D > 0`),
  `Swing.deltaU_mem_den_unstable` and `Swing.deltaS_mem_den_lyapunovStable` (`D ≥ 0`).

Corrections.
* T-vsg-control §1.10 writes `Δθ̇ = Δω`, `2H Δω̇ = −K_E Δθ − D_p Δω` with `Δω` in per unit and
  `Δθ` in rad, which drops the factor `ω_s`.  The correct characteristic polynomial is
  `2H s² + D_p s + ω_s K_E`, so `ω_n² = ω_s K_E / (2H)` and `ζ = D_p / (2 √(2H ω_s K_E))`;
  with the note's data (`H = 2 s`, `K_E = 8`, `ω_s = 2π·50`) `ω_n ≈ 25.07 rad/s`, not
  `1.41 rad/s` (`VSGInfiniteBus.naturalFrequency_numeric`).
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
  /-- The line to the infinite bus, a series RLC branch; its phasor impedance is
  `R + jX` at the grid frequency `ω_s` (lossless). -/
  line : Passive.SeriesRLC
  line_lossless : line.R = 0

/-- The line reactance `X_g` at the grid frequency `ω_s`. -/
abbrev VSGInfiniteBus.Xg (v : VSGInfiniteBus) : ℝ := v.line.reactance v.ωs

namespace VSGInfiniteBus

variable (v : VSGInfiniteBus)

/-- Maximum transferable power `E V_g / X_g`. -/
def Pmax : ℝ := v.E * v.Vg / v.Xg

/-- The VSG closed loop as a sine-curve swing model (`SwingParams.sinusoid`): `M = 2H/ω_s`,
`D = D_p/ω_s`, `P_e(δ) = (E V_g / X_g) sin δ`. -/
def toSwing : SwingParams := .sinusoid (2 * v.H / v.ωs) (v.Dp / v.ωs) v.Pref v.Pmax

/-- Synchronizing coefficient `K_E = (E V_g / X_g) cos δ₀`, that of the swing model. -/
abbrev KE (δ₀ : ℝ) : ℝ := v.toSwing.syncCoeff δ₀

/-- Positivity of the physical parameters. -/
structure Pos : Prop where
  H : 0 < v.H
  ωs : 0 < v.ωs
  E : 0 < v.E
  Vg : 0 < v.Vg
  Xg : 0 < v.Xg

variable {v}

@[tmio M, powerlib_domain] theorem Pos.M (h : v.Pos) : 0 < v.toSwing.M :=
  show 0 < 2 * v.H / v.ωs from div_pos (mul_pos two_pos h.H) h.ωs

@[tmio M, powerlib_domain] theorem Pos.Pmax (h : v.Pos) : 0 < v.Pmax :=
  show 0 < v.E * v.Vg / v.Xg from div_pos (mul_pos h.E h.Vg) h.Xg

variable (v)

/-- Equilibria of the VSG on an infinite bus exist iff `|P_ref| ≤ E V_g / X_g`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (h : v.Pos) :
    (∃ x, v.toSwing.field x = 0) ↔ |v.Pref| ≤ v.Pmax := by
  have := v.toSwing.exists_equilibrium_iff h.M.ne' h.Pmax
  simpa [toSwing] using this

/-- The VSG read about its loading angle `δ₀ = arcsin(P_ref X_g / (E V_g))`. -/
def atLoading : Swing.Model := ⟨v.toSwing, Real.arcsin (v.Pref / v.Pmax)⟩

/-- The VSG read about the second equilibrium angle `π − δ₀`. -/
def atAntiLoading : Swing.Model := ⟨v.toSwing, Real.pi - Real.arcsin (v.Pref / v.Pmax)⟩

/-- The loading angle `δ₀ = arcsin(P_ref X_g / (E V_g))` is locally exponentially stable
(`D_p > 0`, `|P_ref| < E V_g / X_g`). -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable (h : v.Pos) (hD : 0 < v.Dp)
    (hP : |v.Pref| < v.Pmax) :
    connection% (v.atLoading ∈ Swing.family.den (.flow .locallyExponentiallyStable)) := by
  have hD' : 0 < v.toSwing.D := show 0 < v.Dp / v.ωs from div_pos hD h.ωs
  have hP' : |v.toSwing.Pm - v.toSwing.k₁| < v.toSwing.k₂ := by simpa [toSwing] using hP
  have := Swing.deltaS_mem_den_locallyExponentiallyStable v.toSwing h.M hD' h.Pmax hP'
  unfold powerlib.TMIO.Statement at this ⊢
  rw [toSwing, SwingParams.sinusoid_deltaS] at this
  exact this

/-- The second equilibrium `π − δ₀` is unstable for every damping. -/
@[tmio TM, powerlib_domain] theorem unstable (h : v.Pos) (hP : |v.Pref| < v.Pmax) :
    connection% (v.atAntiLoading ∈ Swing.family.den (.flow .unstable)) := by
  have := Swing.deltaU_mem_den_unstable v.toSwing h.M h.Pmax (by simpa [toSwing] using hP)
  unfold powerlib.TMIO.Statement at this ⊢
  rw [toSwing, SwingParams.sinusoid_deltaU] at this
  exact this

/-- Without damping (`D_p = 0`) — and for any `D_p ≥ 0` — the loading angle is Lyapunov
stable (energy function). -/
@[tmio TM, powerlib_domain] theorem lyapunovStable (h : v.Pos) (hD : 0 ≤ v.Dp)
    (hP : |v.Pref| < v.Pmax) :
    connection% (v.atLoading ∈ Swing.family.den (.flow .lyapunovStable)) := by
  have hD' : 0 ≤ v.toSwing.D := show 0 ≤ v.Dp / v.ωs from div_nonneg hD h.ωs.le
  have hP' : |v.toSwing.Pm - v.toSwing.k₁| < v.toSwing.k₂ := by simpa [toSwing] using hP
  have := Swing.deltaS_mem_den_lyapunovStable v.toSwing h.M hD' h.Pmax hP'
  unfold powerlib.TMIO.Statement at this ⊢
  rw [toSwing, SwingParams.sinusoid_deltaS] at this
  exact this

/-- Corrected per-unit characteristic polynomial (T-vsg-control §1.10):
`ω_s · M · det(sI − J) = 2H s² + D_p s + ω_s K_E`. -/
@[tmio M, powerlib_domain] theorem characteristic_polynomial (h : v.Pos) (δ₀ : ℝ) (s : ℂ) :
    (v.ωs : ℂ) * ((v.toSwing.M : ℂ) *
        (Linear.characteristicMatrix (v.toSwing.jacobian δ₀) s).det) =
      2 * (v.H : ℂ) * s ^ 2 + (v.Dp : ℂ) * s + (v.ωs : ℂ) * (v.KE δ₀ : ℂ) := by
  rw [v.toSwing.characteristic_polynomial h.M.ne']
  have hω : (v.ωs : ℂ) ≠ 0 := by exact_mod_cast h.ωs.ne'
  simp only [toSwing, KE, SwingParams.sinusoid_M, SwingParams.sinusoid_D,
    SwingParams.sinusoid_syncCoeff]
  push_cast
  field_simp

/-- Linearized VSG about the angle `δ₀`: globally exponentially stable iff `D_p > 0` and
`K_E > 0` (all coefficients of `2H s² + D_p s + ω_s K_E` positive). -/
@[tmio TM, powerlib_domain] theorem linearModel_mem_den_iff (h : v.Pos) (δ₀ : ℝ) :
    connection% (Swing.Model.mk v.toSwing δ₀ ∈
        Swing.Linearized.family.den (.flow .globallyExponentiallyStable) ↔
      Swing.Model.mk v.toSwing δ₀ ∈ {m : Swing.Model | 0 < v.Dp ∧ 0 < v.KE m.δ}) := by
  have := Swing.Linearized.mem_den_iff (Swing.Model.mk v.toSwing δ₀) h.M
  unfold powerlib.TMIO.Statement at this ⊢
  rw [this]
  simp only [Set.mem_ofPred_eq, toSwing, KE, SwingParams.sinusoid_D,
    SwingParams.sinusoid_syncCoeff, div_pos_iff_of_pos_right h.ωs]

/-- Natural frequency of the corrected linearization: `ω_n² = ω_s K_E / (2H)` equals
`det J`. -/
@[tmio M, powerlib_domain] theorem naturalFrequency_sq (h : v.Pos) (δ₀ : ℝ) :
    (v.toSwing.jacobian δ₀).det = v.ωs * v.KE δ₀ / (2 * v.H) := by
  rw [SwingParams.det_jacobian]
  simp only [toSwing, KE, SwingParams.sinusoid_M, SwingParams.sinusoid_syncCoeff]
  have := h.H.ne'; have := h.ωs.ne'
  field_simp

/-- Damping ratio of the corrected linearization: `ζ = −tr J / (2 √det J)`
(`Criteria.dampingRatio`) is `D / (2 √(M K_E)) = D_p / (2 √(2H ω_s K_E))`
(`SwingParams.dampingRatio_jacobian`). -/
@[tmio M, powerlib_domain] theorem dampingRatio_eq (h : v.Pos) (δ₀ : ℝ) (hK : 0 < v.KE δ₀) :
    Criteria.dampingRatio (v.toSwing.jacobian δ₀) =
      v.Dp / (2 * Real.sqrt (2 * v.H * v.ωs * v.KE δ₀)) := by
  have hω := h.ωs
  have hs : Real.sqrt (v.toSwing.M * v.KE δ₀) =
      Real.sqrt (2 * v.H * v.ωs * v.KE δ₀) / v.ωs := by
    rw [show v.toSwing.M * v.KE δ₀ = 2 * v.H * v.ωs * v.KE δ₀ / v.ωs ^ 2 by
        simp only [toSwing, SwingParams.sinusoid_M]; field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hω.le]
  have hpos : 0 < Real.sqrt (2 * v.H * v.ωs * v.KE δ₀) :=
    Real.sqrt_pos.mpr (by have := h.H; positivity)
  rw [v.toSwing.dampingRatio_jacobian h.M hK, hs]
  simp only [toSwing, SwingParams.sinusoid_D]
  field_simp

/-- With the note's data `H = 2 s`, `K_E = 8 pu/rad`, `ω_s = 100π rad/s`, the corrected
natural frequency `√(ω_s K_E / (2H))` lies in `(25, 25.1) rad/s`. -/
@[tmio T, powerlib_foundation] theorem naturalFrequency_numeric :
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

/-- The classical SMIB as a sine-curve swing model (`SwingParams.sinusoid`),
`P_e(δ) = (E' V_∞ / X_d') sin δ`. -/
def toSwing : SwingParams := .sinusoid m.M m.D m.Pm m.Pmax

/-- The parameter map to the port-Hamiltonian classical machine (`ClassicalSMParams`,
`theorem/PowerSystem/Synchronous/PH.lean`) on its physical range `M > 0`, `D ≥ 0`,
`E' V_∞ / X_d' > 0`: synchronizing coefficient `b = E' V_∞ / X_d'`; its swing parameters
`ClassicalSMParams.toSwing` are `m.toSwing` by definition. -/
def toPH (hM : 0 < m.M) (hD : 0 ≤ m.D) (hP : 0 < m.Pmax) : ClassicalSMParams :=
  ⟨m.M, m.D, m.Pmax, m.Pm, hM, hD, hP⟩

/-- An equilibrium with `δ₀ ∈ (−π/2, π/2)` is locally exponentially stable (`M, D > 0`,
`E' V_∞ / X_d' > 0`). -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable (hM : 0 < m.M) (hD : 0 < m.D)
    (hP : 0 < m.Pmax) {δ₀ : ℝ} (hδ : δ₀ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (heq : m.toSwing.field (PhasePlane.mk δ₀ 0) = 0) :
    connection% (Swing.Model.mk m.toSwing δ₀ ∈
      Swing.family.den (.flow .locallyExponentiallyStable)) :=
  Swing.mem_den_locallyExponentiallyStable _ hM hD
    (by simpa using ((m.toSwing.field_eq_zero_iff hM.ne' _).mp heq).2)
    (by simpa [toSwing, SwingParams.syncCoeff] using mul_pos hP (Real.cos_pos_of_mem_Ioo hδ))

/-- An equilibrium with `cos δ₀ < 0` is unstable for every damping. -/
@[tmio TM, powerlib_domain] theorem unstable (hM : 0 < m.M) (hP : 0 < m.Pmax) {δ₀ : ℝ}
    (hδ : Real.cos δ₀ < 0) (heq : m.toSwing.field (PhasePlane.mk δ₀ 0) = 0) :
    connection% (Swing.Model.mk m.toSwing δ₀ ∈ Swing.family.den (.flow .unstable)) :=
  Swing.mem_den_unstable _ hM
    (by simpa using ((m.toSwing.field_eq_zero_iff hM.ne' _).mp heq).2)
    (by simpa [toSwing, SwingParams.syncCoeff] using mul_neg_of_pos_of_neg hP hδ)

/-- Exact overdamping threshold at the stable equilibrium
(damping-class-dichotomy §3): with `μ = 1 − P_m/P_max ∈ (0, 1]`, all eigenvalues of the
linearization at `δ_s` are real iff `D² ≥ 4 M P_max √(μ (2 − μ))`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem eigenvalues_real_iff (hM : 0 < m.M) :
    (∀ (μ : ℂ) (w : Fin 2 → ℂ), w ≠ 0 →
        (m.toSwing.jacobian m.toSwing.deltaS).map (algebraMap ℝ ℂ) *ᵥ w = μ • w → μ.im = 0) ↔
      4 * m.M * m.Pmax * Real.sqrt ((1 - m.Pm / m.Pmax) * (2 - (1 - m.Pm / m.Pmax))) ≤
        m.D ^ 2 := by
  rw [m.toSwing.eigenvalues_real_iff hM, SwingParams.syncCoeff_deltaS]
  simp only [toSwing, SwingParams.sinusoid_M, SwingParams.sinusoid_D, SwingParams.sinusoid_k₂,
    SwingParams.sinusoid_loadRatio]
  rw [show (1 - m.Pm / m.Pmax) * (2 - (1 - m.Pm / m.Pmax)) = 1 - (m.Pm / m.Pmax) ^ 2 by ring]
  simp only [mul_assoc]

end ClassicalSMIB

/-! ## Post-fault SMIB with line resistance -/

/-- Electrical power from the complex power `S̄ = Ē' Ī*`, `Ī = (Ē' − V̄_g)/Z_e`
(generator OUT-positive): with the branch `Z_e(jω) = R_e + j X_e = r e^{jφ}`,
`P_e = Re S̄ = (R_e/r²) E'² + (E' V_g / r) sin(δ − (θ_g + π/2 − φ))`. -/
@[tmio M, powerlib_domain] theorem electricalPower_eq (E V δ θg r φ : ℝ) (Z : Passive.SeriesRLC)
    (ω : ℝ) (hr : 0 < r) (hR : Z.R = r * Real.cos φ) (hX : Z.reactance ω = r * Real.sin φ) :
    ((E : ℂ) * Complex.exp (δ * Complex.I) *
      (starRingEnd ℂ) (((E : ℂ) * Complex.exp (δ * Complex.I) -
        (V : ℂ) * Complex.exp (θg * Complex.I)) / Z.impedance (ω * Complex.I))).re =
      Z.R / r ^ 2 * E ^ 2 + E * V / r * Real.sin (δ - (θg + Real.pi / 2 - φ)) := by
  have hZ : Z.absSq ω = r ^ 2 := by
    rw [Passive.SeriesRLC.absSq, hR, hX]
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq φ
  -- rotate the bus to `V ∠ 0`: `S̄` is invariant under a common phase `e^{jθ_g}`
  set u := Complex.exp (θg * Complex.I)
  set a := (E : ℂ) * Complex.exp (((δ - θg : ℝ) : ℂ) * Complex.I)
  have hu : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hδ : (E : ℂ) * Complex.exp (δ * Complex.I) = u * a := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hS : (E : ℂ) * Complex.exp (δ * Complex.I) *
      (starRingEnd ℂ) (((E : ℂ) * Complex.exp (δ * Complex.I) - (V : ℂ) * u) /
        Z.impedance (ω * Complex.I)) =
      a * (starRingEnd ℂ) ((a - V) / Z.impedance (ω * Complex.I)) := by
    rw [hδ, show u * a - (V : ℂ) * u = u * (a - V) by ring, mul_div_assoc, map_mul]
    linear_combination (a * (starRingEnd ℂ) ((a - V) / Z.impedance (ω * Complex.I))) * hu
  rw [hS, Grid.linePower E V (δ - θg) ω Z (by rw [hZ]; positivity), hZ]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]
  have hsc : Real.sin (δ - (θg + Real.pi / 2 - φ)) = -Real.cos (δ - θg + φ) := by
    rw [show δ - (θg + Real.pi / 2 - φ) = (δ - θg + φ) - Real.pi / 2 by ring,
      Real.sin_sub_pi_div_two]
  rw [hsc, Real.cos_add, hR, hX]
  field_simp
  ring

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

/-- The post-fault line as a series RL branch in per unit: at the per-unit grid frequency
`ω = 1` (`s = j`) its impedance is `Z_e = r cos φ + j r sin φ`. -/
def line : Passive.SeriesRLC := ⟨m.r * Real.cos m.φ, m.r * Real.sin m.φ, 0⟩

/-- `(k₁, k₂, k₃) = (G_e E'², E' V_g / |Z_e|, θ_g + π/2 − φ)`, `G_e = cos φ / |Z_e|`. -/
def toSwing : SwingParams :=
  ⟨m.M, m.D, m.Pm, Real.cos m.φ / m.r * m.E' ^ 2, m.E' * m.Vg / m.r,
    m.θg + Real.pi / 2 - m.φ⟩

/-- The classical SMIB model is the lossless slice of the post-fault model: a purely reactive
line (`φ = π/2`, `|Z_e| = X_d'`) to the bus `V_∞ ∠ 0` gives the classical swing parameters. -/
@[tmio M, powerlib_domain] theorem toSwing_classical (c : ClassicalSMIB) :
    (⟨c.M, c.D, c.Pm, c.E', c.Vinf, 0, c.Xd', Real.pi / 2⟩ : PostFaultSMIB).toSwing =
      c.toSwing := by
  simp [toSwing, ClassicalSMIB.toSwing, ClassicalSMIB.Pmax, SwingParams.sinusoid]

/-- The power-angle curve of the post-fault model is the real part of the complex power. -/
@[tmio M, powerlib_domain] theorem Pe_eq_complexPower (hr : 0 < m.r) (δ : ℝ) :
    m.toSwing.Pe δ =
      ((m.E' : ℂ) * Complex.exp (δ * Complex.I) *
        (starRingEnd ℂ) (((m.E' : ℂ) * Complex.exp (δ * Complex.I) -
          (m.Vg : ℂ) * Complex.exp (m.θg * Complex.I)) / m.line.impedance Complex.I)).re := by
  have h := electricalPower_eq m.E' m.Vg δ m.θg m.r m.φ m.line 1 hr rfl
    (by simp [line, Passive.SeriesRLC.reactance])
  rw [Complex.ofReal_one, one_mul] at h
  rw [h]
  simp only [line]
  simp only [SwingParams.Pe, toSwing]
  field_simp

end PostFaultSMIB

end powerlib.Synchronous
