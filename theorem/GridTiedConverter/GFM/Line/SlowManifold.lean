import theorem.GridTiedConverter.GFM.Line.VSM

/-! # The slow manifold of the GFM on a dynamic line: first-order correction and line damping

Static identities on the line current of `theorem/GridTiedConverter/GFM/Line/Model.lean` that
organize the time-scale separation between the line (fast, poles `−R/L ± j ω₀`) and the
synchronization law (slow): the zeroth-order slow manifold is the quasi-steady current
`i = i_s(δ)`, its first-order correction is `h₁(δ, ω) = −j L E e^{jδ} ω/Z²`, and on the corrected
manifold the exported power loses exactly `D_line ω`, `D_line = 2 E² R X L/|Z|⁴`: the
first-order slow model is the reduced model with the damping `D − D_line`.

Scope.
* Model boundary of `theorem/GridTiedConverter/GFM/Line/Model.lean` (grid dq frame at `ω₀`,
  export-positive power, constant `E`, R–L line, no inner loops). The statements are algebraic
  and differential identities at a point `(δ, ω)`; with `ε = 1/ω₀` at fixed `R, X` (`L = ε X`)
  the correction `h₁` is the `O(ε)` term of the slow manifold. No statement here bounds the
  `O(ε²)` remainder or the distance of trajectories (no Tikhonov theorem is asserted); the
  generic singular-perturbation laws are `theorem/Dynamics/SingularPerturbation/`.

Source: study note `gfm/t4-timescale/REPORT.md` (a) and its script `t4_01_slow_manifold.py`
(discovery evidence only).

Results.
* `Network.isHurwitz_lineJacobian_iff`: the line block is Hurwitz iff `R > 0` (normal
  hyperbolicity of the slow manifold, uniformly in `ω₀`).
* `Network.hasDerivAt_is`: `i_s'(δ) = j E e^{jδ}/Z`; `Network.line_residual_h1`: on
  `i = i_s(δ) + h₁(δ, ω)` the line equation `L i̇ = E e^{jδ} − V − Z i` along `δ̇ = ω` leaves the
  residual `L ω i_s'(δ)`, i.e. `Z h₁ = −L ω i_s'(δ)`: `h₁` solves the first-order invariance
  equation.
* `Network.hasDerivAt_ownPhasor`: `h₁(δ, ω) / ω` is the derivative at `ω = 0` of the phasor
  current `E e^{jδ}/(R + j(ω₀ + ω)L)` at the converter's own frequency, so `i_s + h₁` is the
  first-order Taylor polynomial of the phasor current with the source at `ω₀ + ω` (`V/Z` fixed).
* `Network.h1_re`, `Network.h1_im` (closed forms) and `Network.power_slowManifold`: the exported
  power on the corrected manifold is `P(δ) − D_line ω` exactly.
* First-order slow models: `VSM.firstOrderField_eq_swing` (the slow rows on the corrected
  manifold are the swing equation with damping `D − D_line`), `VSMLPF.field_qss1_two` (the
  filter row `ω_c (P(δ) − D_line ω − P_f)`), `PSC.field_qss1_zero` (the angle row
  `K_p (P_ref − P(δ) + D_line ω)`, i.e. droop `D = 1/K_p` reduced to `D − D_line`).
-/

noncomputable section
namespace powerlib.GFM.Line
open powerlib.Dynamics (State)

namespace Network

variable (N : Network)

/-- **Normal hyperbolicity**: the fast (line) subsystem is attracting — its Jacobian
`[[−σ, X/L], [−X/L, −σ]]` is Hurwitz, poles `−R/L ± j X/L` — iff the line is resistive, `R > 0`.
Uniformly in `ω₀` the slow manifold is normally hyperbolic exactly for a lossy line. -/
@[tmio M, powerlib_domain] theorem isHurwitz_lineJacobian_iff (hL : 0 < N.L) (hX : N.X ≠ 0) :
    LinearSystems.IsHurwitz N.lineJacobian ↔ 0 < N.R := by
  rw [Criteria.isHurwitz_fin_two_iff, trace_lineJacobian, det_lineJacobian]
  have hXL : N.X / N.L ≠ 0 := div_ne_zero hX hL.ne'
  have hρ : 0 < N.ρ := by
    have h2 : 0 < (N.X / N.L) ^ 2 := by positivity
    unfold ρ; nlinarith [sq_nonneg N.σ]
  constructor
  · rintro ⟨h, -⟩
    have : 0 < N.σ := by linarith
    exact (div_pos_iff_of_pos_right hL).mp this
  · intro hR
    exact ⟨by have : 0 < N.σ := div_pos hR hL; linarith, hρ⟩

/-- First-order correction of the slow manifold, `h₁(δ, ω) = −j L E e^{jδ} ω/Z²`. -/
def h1 (δ ω : ℝ) : ℂ :=
  -(Complex.I * N.L * N.E * Complex.exp (δ * Complex.I) * ω) / (N.Z * N.Z)

/-- The slope of the quasi-steady current, `i_s'(δ) = j E e^{jδ}/Z`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_is (δ : ℝ) :
    HasDerivAt N.is (Complex.I * N.E * Complex.exp (δ * Complex.I) / N.Z) δ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) Complex.I δ := by
    simpa using (hasDerivAt_id δ).ofReal_comp.mul_const Complex.I
  have h3 := ((h1.cexp.const_mul (N.E : ℂ)).sub_const (N.V : ℂ)).div_const N.Z
  convert h3 using 1
  · funext x; simp only [is]
  · ring

/-- **First-order invariance**: on `i = i_s(δ) + h₁(δ, ω)` the line right-hand side
`E e^{jδ} − V − Z i` equals `L ω i_s'(δ)`, the line's `L d/dt i_s(δ)` along `δ̇ = ω`. -/
@[tmio M, powerlib_domain] theorem line_residual_h1 (hZ : N.Z ≠ 0) (δ ω : ℝ) :
    (N.E : ℂ) * Complex.exp (δ * Complex.I) - N.V - N.Z * (N.is δ + N.h1 δ ω) =
      N.L * ω * (Complex.I * N.E * Complex.exp (δ * Complex.I) / N.Z) := by
  simp only [is, h1]
  field_simp
  ring

/-- **The correction is the own-frequency phasor**: `h₁(δ, 1)` is the derivative at `ω = 0` of
the phasor current `E e^{jδ}/(R + j(ω₀ + ω)L)` of the source at the frequency `ω₀ + ω`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_ownPhasor (hZ : N.Z ≠ 0) (δ : ℝ) :
    HasDerivAt (fun w : ℝ => (N.E : ℂ) * Complex.exp (δ * Complex.I) /
      ((N.R : ℂ) + (((N.ω0 + w) * N.L : ℝ) : ℂ) * Complex.I)) (N.h1 δ 1) 0 := by
  have hd : HasDerivAt (fun w : ℝ => (N.R : ℂ) + (((N.ω0 + w) * N.L : ℝ) : ℂ) * Complex.I)
      ((N.L : ℂ) * Complex.I) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).const_add N.ω0).mul_const N.L).ofReal_comp.mul_const
      Complex.I).const_add (N.R : ℂ)
    convert h using 1 <;> simp
  have h0 : (N.R : ℂ) + (((N.ω0 + 0) * N.L : ℝ) : ℂ) * Complex.I = N.Z := by
    simp [Z, X]
  have h := (hasDerivAt_const (0 : ℝ) ((N.E : ℂ) * Complex.exp (δ * Complex.I))).div hd
    (by rw [h0]; exact hZ)
  convert h using 1
  rw [h0, h1]
  push_cast
  field_simp
  ring

@[tmio M, powerlib_domain] theorem h1_re (hZ : N.absSq ≠ 0) (δ ω : ℝ) :
    (N.h1 δ ω).re = N.E * N.L * ω * (N.R ^ 2 * Real.sin δ - 2 * N.R * N.X * Real.cos δ -
      N.X ^ 2 * Real.sin δ) / N.absSq ^ 2 := by
  have hn : Complex.normSq N.Z = N.absSq := by simp [Z, Complex.normSq_apply, absSq]; ring
  rw [h1, Complex.div_re, Complex.normSq_mul, hn]
  simp [Z, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem h1_im (hZ : N.absSq ≠ 0) (δ ω : ℝ) :
    (N.h1 δ ω).im = -(N.E * N.L * ω * (N.R ^ 2 * Real.cos δ + 2 * N.R * N.X * Real.sin δ -
      N.X ^ 2 * Real.cos δ)) / N.absSq ^ 2 := by
  have hn : Complex.normSq N.Z = N.absSq := by simp [Z, Complex.normSq_apply, absSq]; ring
  rw [h1, Complex.div_im, Complex.normSq_mul, hn]
  simp [Z, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  field_simp
  ring

/-- **Line damping**: on the corrected slow manifold the exported power is `P(δ) − D_line ω`,
`D_line = 2 E² R X L/|Z|⁴`. -/
@[tmio M, powerlib_domain] theorem power_slowManifold (hZ : N.absSq ≠ 0) (δ ω : ℝ) :
    N.power δ (N.is δ + N.h1 δ ω).re (N.is δ + N.h1 δ ω).im = N.qssPower δ - N.Dline * ω := by
  rw [Complex.add_re, Complex.add_im, qssPower, power_eq, power_eq, N.h1_re hZ, N.h1_im hZ,
    Dline]
  have hS : N.absSq ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  field_simp
  linear_combination (-(2 * N.E ^ 2 * N.L * ω * N.R * N.X)) * Real.sin_sq_add_cos_sq δ

end Network

namespace VSM

variable (g : VSM)

/-- The corrected slow manifold over `(δ, ω)`: the current at `i_s(δ) + h₁(δ, ω)`. -/
def qss1 (y : State 2) : State 4 :=
  WithLp.toLp 2 ![y 0, y 1, (g.is (y 0) + g.h1 (y 0) (y 1)).re,
    (g.is (y 0) + g.h1 (y 0) (y 1)).im]

/-- The first-order slow model, *defined* as the slow rows of the full field on the corrected
manifold. -/
def firstOrderField (y : State 2) : State 2 :=
  WithLp.toLp 2 ![g.field (g.qss1 y) 0, g.field (g.qss1 y) 1]

/-- The swing machine of the first-order model: damping `D − D_line`. -/
def swingParams1 : Synchronous.SwingParams := ⟨g.M, g.D - g.Dline, g.Pref, g.c0, g.A, g.α⟩

/-- **First-order correction of the reduction**: the slow rows on the corrected manifold are the
swing equation with the damping `D − D_line`. -/
@[tmio M, powerlib_domain] theorem firstOrderField_eq_swing (hZ : 0 < g.absSq) :
    g.firstOrderField = g.swingParams1.field := by
  funext y
  ext i
  fin_cases i
  · simp [firstOrderField, qss1]
  · have hP := g.power_slowManifold hZ.ne' (y 0) (y 1)
    have hp := g.qssPower_eq_polar hZ (y 0)
    show (g.Pref - g.power (y 0) (g.is (y 0) + g.h1 (y 0) (y 1)).re
        (g.is (y 0) + g.h1 (y 0) (y 1)).im - g.D * y 1) / g.M =
      (g.Pref - (g.c0 + g.A * Real.sin (y 0 - g.α)) - (g.D - g.Dline) * y 1) / g.M
    rw [hP, hp]; ring

end VSM

namespace VSMLPF

variable (g : VSMLPF)

/-- The corrected slow manifold over `(δ, ω, P_f)`. -/
def qss1 (y : State 3) : State 5 :=
  WithLp.toLp 2 ![y 0, y 1, y 2, (g.is (y 0) + g.h1 (y 0) (y 1)).re,
    (g.is (y 0) + g.h1 (y 0) (y 1)).im]

/-- **First-order filter row**: on the corrected manifold the filter is driven by
`P(δ) − D_line ω`. -/
@[tmio M, powerlib_domain] theorem field_qss1_two (hZ : g.absSq ≠ 0) (y : State 3) :
    g.field (g.qss1 y) 2 = g.ωc * (g.qssPower (y 0) - g.Dline * y 1 - y 2) := by
  have hP := g.power_slowManifold hZ (y 0) (y 1)
  show g.ωc * (g.power (y 0) (g.is (y 0) + g.h1 (y 0) (y 1)).re
    (g.is (y 0) + g.h1 (y 0) (y 1)).im - y 2) = _
  rw [hP]

end VSMLPF

namespace PSC

variable (g : PSC)

/-- The corrected slow manifold at the angle `δ` and the frequency deviation `ω = δ̇`. -/
def qss1 (δ ω : ℝ) : State 3 :=
  WithLp.toLp 2 ![δ, (g.is δ + g.h1 δ ω).re, (g.is δ + g.h1 δ ω).im]

/-- **First-order angle row**: on the corrected manifold the angle rate is
`K_p (P_ref − P(δ) + D_line ω)`; with `ω = δ̇` the droop `D = 1/K_p` becomes `D − D_line`. -/
@[tmio M, powerlib_domain] theorem field_qss1_zero (hZ : g.absSq ≠ 0) (δ ω : ℝ) :
    g.field (g.qss1 δ ω) 0 = g.Kp * (g.Pref - g.qssPower δ + g.Dline * ω) := by
  have hP := g.power_slowManifold hZ δ ω
  show g.Kp * (g.Pref - g.power δ (g.is δ + g.h1 δ ω).re (g.is δ + g.h1 δ ω).im) = _
  rw [hP]; ring

end PSC

end powerlib.GFM.Line
