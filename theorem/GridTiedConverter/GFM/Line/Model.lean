import theorem.PowerSystem.Synchronous.Swing
import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.GridTiedConverter.GFM.PSC
import theorem.Grid.PowerFlow
import theorem.Transform.ComplexPower
import theorem.Dynamics.Coordinates

/-! # Grid-forming source on a dynamic R–L line to a stiff grid, and its phasor limit

The Layer-0 grid-forming converter: an ideal voltage source `E e^{jδ}` synchronized by active
power, behind a series R–L line with its electromagnetic dynamics, to a stiff grid `V ∠ 0`. Three
synchronization laws: the virtual synchronous machine (`Line.VSM`, four states), the VSM with a
first-order power filter (`Line.VSMLPF`, five states, equivalently droop + LPF) and power
synchronization / pure droop (`Line.PSC`, three states). The module fixes the fields, their
Jacobians (by `fderiv`), the quasi-steady (phasor) current, the equilibria and the quasi-static
(Layer-1) reduction, read as the library's swing, VSM + power-filter and PSC models.

Model boundary.
* Frame: dq frame rotating at the nominal grid frequency `ω₀`, aligned with the stiff grid voltage
  `V ∠ 0`; `δ` is the angle of the internal EMF relative to the grid (rad), `ω = δ̇` the frequency
  deviation (rad/s). Complex notation `i = i_d + j i_q`.
* Line (`Line.Network`): `L i̇ = E e^{jδ} − V − (R + jX) i`, `X = ω₀ L`, i.e.
  `L i̇_d = E cos δ − V − R i_d + X i_q`, `L i̇_q = E sin δ − R i_q − X i_d`. The current `i`
  flows out of the converter into the grid; active power is export-positive (the library's GFM
  convention, `theorem/GridTiedConverter/GFM/VSMLPF.lean`): `P_e + j Q_e = E e^{jδ} · conj i`, the
  per-unit `Transform.pq` of the EMF and the export current (no factor `3/2`; the SI power of an
  amplitude-invariant Park frame is `(3/2) P_e`, `Transform.activePower_eq_re`). At `R = 0` the
  quasi-steady power is `(E V / X) sin δ`, the `K₀ sin δ` of `GFM.VSMLPF` and `P_max sin δ` of
  `GFM.PSC`.
* States, in this order: `Line.VSM` `(δ, ω, i_d, i_q) : State 4`,
  `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`; `Line.VSMLPF` `(δ, ω, P_f, i_d, i_q) : State 5`,
  `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P_e − P_f)` (droop + LPF is this law with `M = τ_p K_R`,
  `D = K_R`, `theorem/GridTiedConverter/GFM/DroopVSM.lean`); `Line.PSC` `(δ, i_d, i_q) : State 3`,
  `δ̇ = K_p (P_ref − P_e)` (pure droop with `K_p = 1/D`).
* Parameters: `E, V > 0` (constant EMF magnitude, stiff grid), `R ≥ 0`, `L, ω₀ > 0`, inertia
  `M > 0`, damping `D > 0`, filter bandwidth `ω_c > 0`, droop gain `K_p > 0`, set-point `P_ref`
  (`Line.Network.Physical` records the network part; each statement lists what it uses).
* Continuous time, autonomous, constant inputs. Excluded: reactive-power / voltage loop
  (constant `E`), inner voltage and current loops, LC filter, current limiting, PLL, delay, PWM,
  grid-frequency variation.
* Level: fields, Jacobians, equilibria, the quasi-steady set and the static reduction. No
  dynamical approximation (Tikhonov, averaging) is asserted here.

Source: study note `gfm/base-model.md` (Layer 0, Layer 1) and `gfm/t4-timescale/REPORT.md` (a);
the R–L line in dq, `L i' = v − R i − ω L J i` (`theorem/Passive/Dq.lean`); the phasor line power
`S̄ = Ē Ī*` (`theorem/Grid/PowerFlow.lean`, `Grid.lineP`).

Results.
* Electrical power `Network.power`, `Network.reactive` (`Network.power_eq`,
  `Network.reactive_eq`); the line rates `Network.rateD`, `Network.rateQ`; their derivatives in any
  state dimension (`Network.hasFDerivAt_power`, `Network.hasFDerivAt_rateD`,
  `Network.hasFDerivAt_rateQ`: `∂P_e/∂δ = −Q_e`).
* Quasi-steady current `Network.is δ = (E e^{jδ} − V)/(R + jX)` (`Network.is_re`,
  `Network.is_im`); the line is at rest iff `i = i_s(δ)` (`Network.rate_eq_zero_iff`).
* Quasi-steady power and reactive power `Network.qssPower`, `Network.qssReactive`: the line power
  of `theorem/Grid/PowerFlow.lean` (`Network.qssPower_eq_lineP`, `Network.qssReactive_eq_lineQ`),
  the one-harmonic form `P(δ) = c₀ + A sin(δ − α)`, `c₀ = E² R/|Z|²`, `A = E V/|Z|`,
  `α = arg(X + jR)` (`Network.qssPower_eq_polar`), synchronizing coefficient
  `K(δ) = A cos(δ − α) = P'(δ)` (`Network.hasDerivAt_qssPower`) and
  `K(δ) + Q(δ) = κ = E² X/|Z|²` (`Network.syncCoeff_add_qssReactive`); the lossless values
  `c₀ = 0`, `A = E V/X`, `α = 0` (`Network.c0_of_lossless`, `Network.A_of_lossless`,
  `Network.α_of_lossless`).
* For each law: the field and its smoothness, the Jacobian by `fderiv` (`VSM.hasFDerivAt_field`,
  `VSMLPF.hasFDerivAt_field`, `PSC.hasFDerivAt_field`), the equilibria (`ω = 0`, `P_f = P_ref`,
  `i = i_s(δ*)`, `P(δ*) = P_ref`: `VSM.field_eq_zero_iff`, `VSMLPF.field_eq_zero_iff`,
  `PSC.field_eq_zero_iff`) and their existence `|P_ref − c₀| ≤ A`
  (`VSM.exists_equilibrium_iff`).
* Quasi-static reduction (Layer 1): the reduced field is *defined* as the slow rows evaluated on
  the quasi-steady set; it is the swing equation `SwingParams ⟨M, D, P_ref, c₀, A, α⟩`
  (`VSM.reducedField_eq_swing`), the lossless VSM + power filter `GFM.VSMLPF ⟨M, D, ω_c, P_ref,
  E V/X⟩` (`VSMLPF.reducedField_eq_vsmlpf`, `R = 0`) and the PSC law
  `GFM.PSC ⟨K_p, P_ref − c₀, A⟩` in the angle `δ − α` (`PSC.reducedRhs_eq_shift`; lossless:
  `PSC.reducedField_eq_psc`). Selected-angle models `VSM.Model`, `VSMLPF.Model`, `PSC.Model`
  with their operating points `(δ*, 0, i_s(δ*))`, `(δ*, 0, P_ref, i_s(δ*))`, `(δ*, i_s(δ*))`
  (`VSM.Model.field_point_eq_zero_iff` and its analogues).

Family and connection conclusions.
The module defines no family and states no behaviour: every result is static evidence on the
model. The families of the three laws and their connection conclusions are in
`theorem/GridTiedConverter/GFM/Line/VSM.lean` and `theorem/GridTiedConverter/GFM/Line/PSC.lean`.
-/

noncomputable section
namespace powerlib.GFM.Line
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)

/-! ## The source, the line and the grid -/

/-- Internal EMF magnitude `E`, grid voltage `V`, line resistance `R`, line inductance `L` and
nominal frequency `ω₀`. -/
structure Network where
  E : ℝ
  V : ℝ
  R : ℝ
  L : ℝ
  ω0 : ℝ

namespace Network

variable (N : Network)

/-- Physical network parameters: `E, V > 0`, `R ≥ 0`, `L, ω₀ > 0`. -/
structure Physical : Prop where
  E : 0 < N.E
  V : 0 < N.V
  R : 0 ≤ N.R
  L : 0 < N.L
  ω0 : 0 < N.ω0

/-- Line reactance `X = ω₀ L`. -/
def X : ℝ := N.ω0 * N.L

/-- The line as a series R–L element (`theorem/Passive/Series.lean`, no capacitor). -/
def branch : Passive.SeriesRLC := ⟨N.R, N.L, 0⟩

/-- Squared impedance magnitude `|Z|² = R² + X²`. -/
def absSq : ℝ := N.R ^ 2 + N.X ^ 2

/-- The line impedance at the nominal frequency, `Z = R + jX`. -/
def Z : ℂ := N.R + N.X * Complex.I

/-- The internal EMF `E e^{jδ}` in grid dq components. -/
def emf (δ : ℝ) : Fin 2 → ℝ := ![N.E * Real.cos δ, N.E * Real.sin δ]

/-- Exported active power `P_e = Re(E e^{jδ} conj i)` (`Transform.pq`). -/
def power (δ id iq : ℝ) : ℝ := Transform.pq (N.emf δ) ![id, iq] 0

/-- Exported reactive power `Q_e = Im(E e^{jδ} conj i)` (`Transform.pq`). -/
def reactive (δ id iq : ℝ) : ℝ := Transform.pq (N.emf δ) ![id, iq] 1

/-- The d-axis line rate `i̇_d = (E cos δ − V − R i_d + X i_q)/L`. -/
def rateD (δ id iq : ℝ) : ℝ := (N.E * Real.cos δ - N.V - N.R * id + N.X * iq) / N.L

/-- The q-axis line rate `i̇_q = (E sin δ − R i_q − X i_d)/L`. -/
def rateQ (δ id iq : ℝ) : ℝ := (N.E * Real.sin δ - N.R * iq - N.X * id) / N.L

@[tmio M, powerlib_domain] theorem power_eq (δ id iq : ℝ) :
    N.power δ id iq = N.E * (Real.cos δ * id + Real.sin δ * iq) := by
  simp [power, Transform.pq, emf]; ring

@[tmio M, powerlib_domain] theorem reactive_eq (δ id iq : ℝ) :
    N.reactive δ id iq = N.E * (Real.sin δ * id - Real.cos δ * iq) := by
  simp [reactive, Transform.pq, emf]; ring

/-- The two powers are the complex power `E e^{jδ} · conj i` of the export current. -/
@[tmio M, powerlib_domain] theorem complexPower_eq (δ id iq : ℝ) :
    ((N.power δ id iq : ℝ) : ℂ) + (N.reactive δ id iq : ℂ) * Complex.I =
      (N.E : ℂ) * Complex.exp (δ * Complex.I) *
        (starRingEnd ℂ) ((id : ℂ) + (iq : ℂ) * Complex.I) := by
  rw [power_eq, reactive_eq]
  apply Complex.ext <;>
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re,
      Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> ring

@[tmio M, powerlib_domain] theorem branch_reactance : N.branch.reactance N.ω0 = N.X := by
  simp [branch, Passive.SeriesRLC.reactance, X]

@[tmio M, powerlib_domain] theorem branch_absSq : N.branch.absSq N.ω0 = N.absSq := by
  unfold Passive.SeriesRLC.absSq; rw [branch_reactance]; rfl

@[tmio M, powerlib_domain] theorem branch_impedance :
    N.branch.impedance (N.ω0 * Complex.I) = N.Z := by
  rw [Passive.SeriesRLC.impedance_jω, branch_reactance]; rfl

variable {N}

@[tmio M, powerlib_domain] theorem Physical.X_pos (h : N.Physical) : 0 < N.X := mul_pos h.ω0 h.L

@[tmio M, powerlib_domain] theorem Physical.absSq_pos (h : N.Physical) : 0 < N.absSq := by
  have := h.X_pos; unfold absSq; positivity

variable (N)

/-! ### Derivatives in any state dimension -/

/-- `∂P_e/∂δ = −Q_e`, `∂P_e/∂i_d = E cos δ`, `∂P_e/∂i_q = E sin δ`, read on three coordinates
`a, b, c` of a state of any dimension. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_power {n : ℕ} (a b c : Fin n) (x : State n) :
    HasFDerivAt (fun y : State n => N.power (y a) (y b) (y c))
      ((-N.reactive (x a) (x b) (x c)) • coord a + (N.E * Real.cos (x a)) • coord b +
        (N.E * Real.sin (x a)) • coord c) x := by
  have ha := hasFDerivAt_coord a x
  have hcos := (Real.hasDerivAt_cos (x a)).comp_hasFDerivAt x ha
  have hsin := (Real.hasDerivAt_sin (x a)).comp_hasFDerivAt x ha
  have h := ((hcos.mul (hasFDerivAt_coord b x)).add
    (hsin.mul (hasFDerivAt_coord c x))).const_mul N.E
  convert h using 1
  · funext y; simp [power_eq]
  · ext v; simp [reactive_eq]; ring

/-- Derivative of the d-axis line rate on three coordinates of a state of any dimension. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_rateD {n : ℕ} (a b c : Fin n) (x : State n) :
    HasFDerivAt (fun y : State n => N.rateD (y a) (y b) (y c))
      ((-(N.E * Real.sin (x a)) / N.L) • coord a + (-N.R / N.L) • coord b +
        (N.X / N.L) • coord c) x := by
  have hcos := (Real.hasDerivAt_cos (x a)).comp_hasFDerivAt x (hasFDerivAt_coord a x)
  have h := ((((hcos.const_mul N.E).sub_const N.V).sub
    ((hasFDerivAt_coord b x).const_mul N.R)).add
    ((hasFDerivAt_coord c x).const_mul N.X)).mul_const N.L⁻¹
  convert h using 1
  · funext y; simp [rateD, div_eq_mul_inv]
  · ext v; simp; ring

/-- Derivative of the q-axis line rate on three coordinates of a state of any dimension. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_rateQ {n : ℕ} (a b c : Fin n) (x : State n) :
    HasFDerivAt (fun y : State n => N.rateQ (y a) (y b) (y c))
      ((N.E * Real.cos (x a) / N.L) • coord a + (-N.X / N.L) • coord b +
        (-N.R / N.L) • coord c) x := by
  have hsin := (Real.hasDerivAt_sin (x a)).comp_hasFDerivAt x (hasFDerivAt_coord a x)
  have h := (((hsin.const_mul N.E).sub
    ((hasFDerivAt_coord c x).const_mul N.R)).sub
    ((hasFDerivAt_coord b x).const_mul N.X)).mul_const N.L⁻¹
  convert h using 1
  · funext y; simp [rateQ, div_eq_mul_inv]
  · ext v; simp; ring

/-! ### The quasi-steady (phasor) current and power -/

/-- The quasi-steady line current `i_s(δ) = (E e^{jδ} − V)/(R + jX)`. -/
def is (δ : ℝ) : ℂ := (N.E * Complex.exp (δ * Complex.I) - N.V) / N.Z

@[tmio M, powerlib_domain] theorem is_re (δ : ℝ) :
    (N.is δ).re = (N.R * (N.E * Real.cos δ - N.V) + N.X * (N.E * Real.sin δ)) / N.absSq := by
  simp [is, Z, Complex.div_re, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, absSq]
  ring

@[tmio M, powerlib_domain] theorem is_im (δ : ℝ) :
    (N.is δ).im = (N.R * (N.E * Real.sin δ) - N.X * (N.E * Real.cos δ - N.V)) / N.absSq := by
  simp [is, Z, Complex.div_im, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, absSq]
  ring

/-- The line is at rest exactly on the quasi-steady current: `i̇ = 0 ⇔ i = i_s(δ)`. -/
@[tmio M, powerlib_domain] theorem rate_eq_zero_iff (hL : N.L ≠ 0) (hZ : N.absSq ≠ 0)
    (δ id iq : ℝ) :
    N.rateD δ id iq = 0 ∧ N.rateQ δ id iq = 0 ↔ id = (N.is δ).re ∧ iq = (N.is δ).im := by
  rw [is_re, is_im]
  simp only [rateD, rateQ, div_eq_zero_iff, hL, or_false]
  unfold absSq at hZ ⊢
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> field_simp
    · linear_combination (-N.R) * h1 + (-N.X) * h2
    · linear_combination N.X * h1 + (-N.R) * h2
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp <;> ring

/-- Quasi-steady active power `P(δ) = P_e(δ, i_s(δ))`. -/
def qssPower (δ : ℝ) : ℝ := N.power δ (N.is δ).re (N.is δ).im

/-- Quasi-steady reactive power `Q(δ) = Q_e(δ, i_s(δ))`. -/
def qssReactive (δ : ℝ) : ℝ := N.reactive δ (N.is δ).re (N.is δ).im

@[tmio M, powerlib_domain] theorem qssPower_eq (hZ : N.absSq ≠ 0) (δ : ℝ) :
    N.qssPower δ = (N.R * (N.E ^ 2 - N.E * N.V * Real.cos δ) +
      N.X * N.E * N.V * Real.sin δ) / N.absSq := by
  rw [qssPower, power_eq, is_re, is_im]
  field_simp
  linear_combination (N.E ^ 2 * N.R) * Real.sin_sq_add_cos_sq δ

@[tmio M, powerlib_domain] theorem qssReactive_eq (hZ : N.absSq ≠ 0) (δ : ℝ) :
    N.qssReactive δ = (N.X * (N.E ^ 2 - N.E * N.V * Real.cos δ) -
      N.R * N.E * N.V * Real.sin δ) / N.absSq := by
  rw [qssReactive, reactive_eq, is_re, is_im]
  field_simp
  linear_combination (N.E ^ 2 * N.X) * Real.sin_sq_add_cos_sq δ

/-- The quasi-steady power is the phasor line power `Grid.lineP` of the R–L branch at `ω₀`. -/
@[tmio M, powerlib_domain] theorem qssPower_eq_lineP (hZ : N.absSq ≠ 0) (δ : ℝ) :
    N.qssPower δ = Grid.lineP N.V N.branch N.ω0 δ N.E := by
  rw [qssPower_eq N hZ, Grid.lineP, branch_reactance, branch_absSq]; rfl

/-- The quasi-steady reactive power is the phasor line power `Grid.lineQ` of the branch. -/
@[tmio M, powerlib_domain] theorem qssReactive_eq_lineQ (hZ : N.absSq ≠ 0) (δ : ℝ) :
    N.qssReactive δ = Grid.lineQ N.V N.branch N.ω0 δ N.E := by
  rw [qssReactive_eq N hZ, Grid.lineQ, branch_reactance, branch_absSq]; rfl

/-- Offset `c₀ = E² R/|Z|²` of the power-angle curve. -/
def c0 : ℝ := N.E ^ 2 * N.R / N.absSq

/-- Amplitude `A = E V/|Z|` of the power-angle curve. -/
def A : ℝ := N.E * N.V / Real.sqrt N.absSq

/-- Phase `α = arg(X + jR)` (`sin α = R/|Z|`, `cos α = X/|Z|`). -/
def α : ℝ := Complex.arg (N.X + N.R * Complex.I)

/-- `κ = E² X/|Z|²`, the sum of the synchronizing coefficient and the reactive power. -/
def κ : ℝ := N.E ^ 2 * N.X / N.absSq

/-- Synchronizing coefficient `K(δ) = A cos(δ − α)`. -/
def syncCoeff (δ : ℝ) : ℝ := N.A * Real.cos (δ - N.α)

@[tmio M, powerlib_domain] private theorem norm_X_add_R :
    ‖(N.X : ℂ) + N.R * Complex.I‖ = Real.sqrt N.absSq := by
  rw [Complex.norm_add_mul_I, absSq, add_comm]

@[tmio M, powerlib_domain] private theorem X_add_R_ne (hZ : 0 < N.absSq) :
    (N.X : ℂ) + N.R * Complex.I ≠ 0 := by
  intro h
  have := N.norm_X_add_R
  rw [h, norm_zero] at this
  exact (Real.sqrt_pos.mpr hZ).ne this

@[tmio M, powerlib_domain] theorem sin_α :
    Real.sin N.α = N.R / Real.sqrt N.absSq := by
  rw [α, Complex.sin_arg, N.norm_X_add_R]; simp

@[tmio M, powerlib_domain] theorem cos_α (hZ : 0 < N.absSq) :
    Real.cos N.α = N.X / Real.sqrt N.absSq := by
  rw [α, Complex.cos_arg (N.X_add_R_ne hZ), N.norm_X_add_R]; simp

/-- **One-harmonic power-angle curve**: `P(δ) = c₀ + A sin(δ − α)` (no `2δ` term). -/
@[tmio M, powerlib_domain] theorem qssPower_eq_polar (hZ : 0 < N.absSq) (δ : ℝ) :
    N.qssPower δ = N.c0 + N.A * Real.sin (δ - N.α) := by
  rw [qssPower_eq N hZ.ne', Real.sin_sub, N.sin_α, N.cos_α hZ, c0, A]
  have hs := Real.sqrt_pos.mpr hZ
  have hss := Real.sq_sqrt hZ.le
  set s := Real.sqrt N.absSq
  rw [← hss]
  field_simp
  ring

/-- The polar form of the reactive power, `Q(δ) = κ − A cos(δ − α)`. -/
@[tmio M, powerlib_domain] theorem qssReactive_eq_polar (hZ : 0 < N.absSq) (δ : ℝ) :
    N.qssReactive δ = N.κ - N.A * Real.cos (δ - N.α) := by
  rw [qssReactive_eq N hZ.ne', Real.cos_sub, N.sin_α, N.cos_α hZ, κ, A]
  have hs := Real.sqrt_pos.mpr hZ
  have hss := Real.sq_sqrt hZ.le
  set s := Real.sqrt N.absSq
  rw [← hss]
  field_simp
  ring

/-- The synchronizing coefficient and the quasi-steady reactive power add up to
`κ = E² X/|Z|²`. -/
@[tmio M, powerlib_domain] theorem syncCoeff_add_qssReactive (hZ : 0 < N.absSq) (δ : ℝ) :
    N.syncCoeff δ + N.qssReactive δ = N.κ := by
  rw [qssReactive_eq_polar N hZ, syncCoeff]; ring

/-- The synchronizing coefficient is the slope of the power-angle curve, `P'(δ) = K(δ)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_qssPower (hZ : 0 < N.absSq) (δ : ℝ) :
    HasDerivAt N.qssPower (N.syncCoeff δ) δ := by
  have h := (((Real.hasDerivAt_sin (δ - N.α)).comp δ
    ((hasDerivAt_id δ).sub_const N.α)).const_mul N.A).const_add N.c0
  convert h using 1
  · funext y; simp [qssPower_eq_polar N hZ]
  · simp [syncCoeff]

variable {N}

/-- Lossless line: no offset. -/
@[tmio M, powerlib_domain] theorem c0_of_lossless (hR : N.R = 0) : N.c0 = 0 := by
  simp [c0, hR]

/-- Lossless line: the amplitude is `E V/X`. -/
@[tmio M, powerlib_domain] theorem A_of_lossless (hR : N.R = 0) (hX : 0 < N.X) :
    N.A = N.E * N.V / N.X := by
  simp [A, absSq, hR, Real.sqrt_sq hX.le]

/-- Lossless line: no phase. -/
@[tmio M, powerlib_domain] theorem α_of_lossless (hR : N.R = 0) (hX : 0 < N.X) : N.α = 0 := by
  simp [α, hR, Complex.arg_ofReal_of_nonneg hX.le]

/-- Lossless line: `P(δ) = (E V/X) sin δ`. -/
@[tmio M, powerlib_domain] theorem qssPower_of_lossless (hR : N.R = 0) (hX : 0 < N.X) (δ : ℝ) :
    N.qssPower δ = N.E * N.V / N.X * Real.sin δ := by
  have hZ : 0 < N.absSq := by unfold absSq; positivity
  rw [qssPower_eq_polar N hZ, c0_of_lossless hR, A_of_lossless hR hX, α_of_lossless hR hX]
  simp

end Network

/-! ## The virtual synchronous machine on the line (four states) -/

/-- VSM on the dynamic line: the network, inertia `M`, damping `D`, set-point `P_ref`. -/
structure VSM extends Network where
  M : ℝ
  D : ℝ
  Pref : ℝ

namespace VSM

variable (g : VSM)

/-- The closed-loop field on `(δ, ω, i_d, i_q)`. -/
def field (x : State 4) : State 4 :=
  WithLp.toLp 2 ![x 1, (g.Pref - g.power (x 0) (x 2) (x 3) - g.D * x 1) / g.M,
    g.rateD (x 0) (x 2) (x 3), g.rateQ (x 0) (x 2) (x 3)]

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 4) :
    g.field x 0 = x 1 := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 4) :
    g.field x 1 = (g.Pref - g.power (x 0) (x 2) (x 3) - g.D * x 1) / g.M := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 4) :
    g.field x 2 = g.rateD (x 0) (x 2) (x 3) := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_three (x : State 4) :
    g.field x 3 = g.rateQ (x 0) (x 2) (x 3) := rfl

/-- The Jacobian at angle `δ` and current `(i_d, i_q)`; the `(1, 0)` entry is `Q_e/M`. -/
def jacobian (δ id iq : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
    g.reactive δ id iq / g.M, -g.D / g.M, -(g.E * Real.cos δ) / g.M, -(g.E * Real.sin δ) / g.M;
    -(g.E * Real.sin δ) / g.L, 0, -g.R / g.L, g.X / g.L;
    g.E * Real.cos δ / g.L, 0, -g.X / g.L, -g.R / g.L]

@[tmio M, powerlib_domain] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k g.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [field, Network.power_eq, Network.rateD, Network.rateQ] <;> fun_prop

@[tmio M, powerlib_domain] theorem hasFDerivAt_field (x : State 4) :
    HasFDerivAt g.field
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (g.jacobian (x 0) (x 2) (x 3))) x := by
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![coord 1, g.M⁻¹ • (-((-g.reactive (x 0) (x 2) (x 3)) • coord 0 +
        (g.E * Real.cos (x 0)) • coord 2 + (g.E * Real.sin (x 0)) • coord 3) - g.D • coord 1),
      (-(g.E * Real.sin (x 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 2 + (g.X / g.L) • coord 3,
      (g.E * Real.cos (x 0) / g.L) • coord 0 + (-g.X / g.L) • coord 2 + (-g.R / g.L) • coord 3]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · exact hasFDerivAt_coord 1 x
    · have h := (((hasFDerivAt_const g.Pref x).sub (g.hasFDerivAt_power 0 2 3 x)).sub
        ((hasFDerivAt_coord 1 x).const_smul g.D)).const_smul g.M⁻¹
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · simp
    · exact g.hasFDerivAt_rateD 0 2 3 x
    · exact g.hasFDerivAt_rateQ 0 2 3 x
  · fin_cases i <;> (simp [jacobian, Fin.sum_univ_four]; try ring)

@[tmio M, powerlib_domain] theorem fderiv_field (x : State 4) :
    fderiv ℝ g.field x =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (g.jacobian (x 0) (x 2) (x 3)) :=
  (g.hasFDerivAt_field x).fderiv

/-- The quasi-steady state over `(δ, ω)`: the current at `i_s(δ)`. -/
def qss (y : State 2) : State 4 :=
  WithLp.toLp 2 ![y 0, y 1, (g.is (y 0)).re, (g.is (y 0)).im]

/-- The line rows vanish exactly on the quasi-steady set. -/
@[tmio M, powerlib_domain] theorem fast_eq_zero_iff (hL : g.L ≠ 0) (hZ : g.absSq ≠ 0)
    (x : State 4) :
    g.field x 2 = 0 ∧ g.field x 3 = 0 ↔ x = g.qss (PhasePlane.mk (x 0) (x 1)) := by
  rw [field_apply_two, field_apply_three, g.rate_eq_zero_iff hL hZ]
  constructor
  · rintro ⟨h2, h3⟩
    ext i; fin_cases i <;> simp [qss, h2, h3]
  · intro h
    rw [h]; simp [qss]

/-- The reduced (Layer-1) field, *defined* as the slow rows `(δ̇, ω̇)` of the full field on the
quasi-steady set. -/
def reducedField (y : State 2) : State 2 :=
  WithLp.toLp 2 ![g.field (g.qss y) 0, g.field (g.qss y) 1]

/-- The swing machine of the reduced model: `M δ̈ + D δ̇ = P_ref − c₀ − A sin(δ − α)`. -/
def swingParams : Synchronous.SwingParams := ⟨g.M, g.D, g.Pref, g.c0, g.A, g.α⟩

/-- **Quasi-static reduction**: the slow rows on the quasi-steady set are the swing equation with
the one-harmonic power-angle curve. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_swing (hZ : 0 < g.absSq) :
    g.reducedField = g.swingParams.field := by
  funext y
  ext i
  fin_cases i
  · simp [reducedField, qss]
  · have hP := g.qssPower_eq_polar hZ (y 0)
    simp only [Network.qssPower] at hP
    simp [reducedField, qss, Synchronous.SwingParams.accel, Synchronous.SwingParams.Pe,
      swingParams, hP]

/-- Equilibria: `ω = 0`, the current at `i_s(δ)` and power balance `P(δ) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : g.absSq ≠ 0) (x : State 4) :
    g.field x = 0 ↔ x 1 = 0 ∧ x 2 = (g.is (x 0)).re ∧ x 3 = (g.is (x 0)).im ∧
      g.qssPower (x 0) = g.Pref := by
  have hrow : g.field x = 0 ↔ g.field x 0 = 0 ∧ g.field x 1 = 0 ∧
      (g.field x 2 = 0 ∧ g.field x 3 = 0) := by
    constructor
    · intro h; simp [h]
    · rintro ⟨h0, h1, h2, h3⟩
      ext i; fin_cases i
      exacts [h0, h1, h2, h3]
  rw [hrow, field_apply_two, field_apply_three, g.rate_eq_zero_iff hL hZ, field_apply_zero,
    field_apply_one, div_eq_zero_iff, or_iff_left hM]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨h0, h2, h3, ?_⟩
    rw [Network.qssPower, ← h2, ← h3]
    rw [h0] at h1
    linarith
  · rintro ⟨h0, h2, h3, h4⟩
    refine ⟨h0, ?_, h2, h3⟩
    rw [Network.qssPower, ← h2, ← h3] at h4
    rw [h0, h4]; ring

/-- Equilibria exist iff the power-angle curve reaches the set-point, `|P_ref − c₀| ≤ A`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hV : 0 < g.E * g.V) :
    (∃ x, g.field x = 0) ↔ |g.Pref - g.c0| ≤ g.A := by
  have hA : 0 < g.A := div_pos hV (Real.sqrt_pos.mpr hZ)
  have key := g.swingParams.exists_equilibrium_iff hM hA
  simp only [swingParams] at key
  rw [← key]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨-, -, -, hP⟩ := (g.field_eq_zero_iff hM hL hZ.ne' x).mp hx
    refine ⟨PhasePlane.mk (x 0) 0, (g.swingParams.field_eq_zero_iff hM _).mpr ⟨by simp, ?_⟩⟩
    simp only [PhasePlane.mk_apply_zero, Synchronous.SwingParams.Pe, swingParams]
    rw [← Network.qssPower_eq_polar _ hZ]; exact hP
  · rintro ⟨y, hy⟩
    obtain ⟨-, hP⟩ := (g.swingParams.field_eq_zero_iff hM y).mp hy
    refine ⟨g.qss (PhasePlane.mk (y 0) 0), (g.field_eq_zero_iff hM hL hZ.ne' _).mpr ?_⟩
    simp only [qss, PhasePlane.mk_apply_zero]
    refine ⟨by simp, by simp, by simp, ?_⟩
    simp only [Synchronous.SwingParams.Pe, swingParams] at hP
    simpa [Network.qssPower_eq_polar _ hZ] using hP

/-- A VSM on the line read about a selected angle `δ*`. -/
structure Model where
  /-- The parameters. -/
  g : VSM
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The operating point `(δ*, 0, i_s(δ*))`. -/
def Model.point (m : Model) : State 4 := m.g.qss (PhasePlane.mk m.δ 0)

/-- The field translated so that the operating point is the origin. -/
def Model.field (m : Model) (z : State 4) : State 4 := m.g.field (z + m.point)

/-- The reduced (swing) model at the same angle. -/
def Model.toSwing (m : Model) : Synchronous.Swing.Model := ⟨m.g.swingParams, m.δ⟩

/-- The operating point is an equilibrium iff the angle is balanced, `P(δ*) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.field_point_eq_zero_iff (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : m.g.absSq ≠ 0) :
    m.g.field m.point = 0 ↔ m.g.qssPower m.δ = m.g.Pref := by
  rw [m.g.field_eq_zero_iff hM hL hZ]
  simp [Model.point, qss]

@[tmio M, powerlib_domain] theorem Model.contDiff_field (m : Model) : ContDiff ℝ 1 m.field :=
  m.g.contDiff_field.comp (contDiff_id.add contDiff_const)

end VSM

/-! ## The VSM with a first-order power filter on the line (five states) -/

/-- VSM + power filter (droop + LPF) on the dynamic line: the VSM data and the filter bandwidth
`ω_c`. -/
structure VSMLPF extends VSM where
  ωc : ℝ

namespace VSMLPF

variable (g : VSMLPF)

/-- The closed-loop field on `(δ, ω, P_f, i_d, i_q)`. -/
def field (x : State 5) : State 5 :=
  WithLp.toLp 2 ![x 1, (g.Pref - x 2 - g.D * x 1) / g.M,
    g.ωc * (g.power (x 0) (x 3) (x 4) - x 2), g.rateD (x 0) (x 3) (x 4),
    g.rateQ (x 0) (x 3) (x 4)]

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 5) :
    g.field x 0 = x 1 := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 5) :
    g.field x 1 = (g.Pref - x 2 - g.D * x 1) / g.M := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 5) :
    g.field x 2 = g.ωc * (g.power (x 0) (x 3) (x 4) - x 2) := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_three (x : State 5) :
    g.field x 3 = g.rateD (x 0) (x 3) (x 4) := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_four (x : State 5) :
    g.field x 4 = g.rateQ (x 0) (x 3) (x 4) := rfl

/-- The Jacobian at angle `δ` and current `(i_d, i_q)`; the `(2, 0)` entry is `−ω_c Q_e`. -/
def jacobian (δ id iq : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 0;
    0, -g.D / g.M, -1 / g.M, 0, 0;
    -(g.ωc * g.reactive δ id iq), 0, -g.ωc, g.ωc * (g.E * Real.cos δ),
      g.ωc * (g.E * Real.sin δ);
    -(g.E * Real.sin δ) / g.L, 0, 0, -g.R / g.L, g.X / g.L;
    g.E * Real.cos δ / g.L, 0, 0, -g.X / g.L, -g.R / g.L]

@[tmio M, powerlib_domain] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k g.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [field, Network.power_eq, Network.rateD, Network.rateQ] <;> fun_prop

@[tmio M, powerlib_domain] theorem hasFDerivAt_field (x : State 5) :
    HasFDerivAt g.field
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.jacobian (x 0) (x 3) (x 4))) x := by
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![coord 1, g.M⁻¹ • (-coord 2 - g.D • coord 1),
      g.ωc • ((-g.reactive (x 0) (x 3) (x 4)) • coord 0 + (g.E * Real.cos (x 0)) • coord 3 +
        (g.E * Real.sin (x 0)) • coord 4 - coord 2),
      (-(g.E * Real.sin (x 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 3 + (g.X / g.L) • coord 4,
      (g.E * Real.cos (x 0) / g.L) • coord 0 + (-g.X / g.L) • coord 3 + (-g.R / g.L) • coord 4]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · exact hasFDerivAt_coord 1 x
    · have h := (((hasFDerivAt_const g.Pref x).sub (hasFDerivAt_coord 2 x)).sub
        ((hasFDerivAt_coord 1 x).const_smul g.D)).const_smul g.M⁻¹
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp
    · have h := ((g.hasFDerivAt_power 0 3 4 x).sub (hasFDerivAt_coord 2 x)).const_smul g.ωc
      convert h using 1
      · funext y; simp
      · simp
    · exact g.hasFDerivAt_rateD 0 3 4 x
    · exact g.hasFDerivAt_rateQ 0 3 4 x
  · fin_cases i <;> simp [jacobian, Fin.sum_univ_five] <;> ring

@[tmio M, powerlib_domain] theorem fderiv_field (x : State 5) :
    fderiv ℝ g.field x =
      Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.jacobian (x 0) (x 3) (x 4)) :=
  (g.hasFDerivAt_field x).fderiv

/-- The quasi-steady state over `(δ, ω, P_f)`: the current at `i_s(δ)`. -/
def qss (y : State 3) : State 5 :=
  WithLp.toLp 2 ![y 0, y 1, y 2, (g.is (y 0)).re, (g.is (y 0)).im]

/-- The reduced (Layer-1) field, *defined* as the slow rows `(δ̇, ω̇, Ṗ_f)` of the full field on
the quasi-steady set. -/
def reducedField (y : State 3) : State 3 :=
  WithLp.toLp 2 ![g.field (g.qss y) 0, g.field (g.qss y) 1, g.field (g.qss y) 2]

/-- The library's three-state VSM + power-filter parameters of a lossless line,
`K₀ = E V/X`. -/
def toLossless : powerlib.GFM.VSMLPF := ⟨g.M, g.D, g.ωc, g.Pref, g.E * g.V / g.X⟩

/-- **Quasi-static reduction, lossless line**: the slow rows on the quasi-steady set are the
three-state VSM + power-filter field `GFM.VSMLPF ⟨M, D, ω_c, P_ref, E V/X⟩`. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_vsmlpf (hR : g.R = 0) (hX : 0 < g.X) :
    g.reducedField = g.toLossless.field := by
  funext y
  ext i
  fin_cases i
  · simp [reducedField, qss, toLossless]
  · simp [reducedField, qss, toLossless]
  · simp only [reducedField, Fin.reduceFinMk, Fin.isValue, field_apply_two]
    have hP := g.qssPower_of_lossless hR hX (y 0)
    simp only [Network.qssPower] at hP
    simp [qss, toLossless, hP]

/-- Equilibria: `ω = 0`, `P_f = P_ref`, the current at `i_s(δ)` and `P(δ) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hL : g.L ≠ 0) (hZ : g.absSq ≠ 0) (x : State 5) :
    g.field x = 0 ↔ x 1 = 0 ∧ x 2 = g.Pref ∧ x 3 = (g.is (x 0)).re ∧
      x 4 = (g.is (x 0)).im ∧ g.qssPower (x 0) = g.Pref := by
  have hrow : g.field x = 0 ↔ g.field x 0 = 0 ∧ g.field x 1 = 0 ∧ g.field x 2 = 0 ∧
      (g.field x 3 = 0 ∧ g.field x 4 = 0) := by
    constructor
    · intro h; simp [h]
    · rintro ⟨h0, h1, h2, h3, h4⟩
      ext i; fin_cases i
      exacts [h0, h1, h2, h3, h4]
  rw [hrow, field_apply_three, field_apply_four, g.rate_eq_zero_iff hL hZ, field_apply_zero,
    field_apply_one, field_apply_two, div_eq_zero_iff, or_iff_left hM, mul_eq_zero,
    or_iff_right hω]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    rw [h0] at h1
    refine ⟨h0, by linarith, h3, h4, ?_⟩
    rw [Network.qssPower, ← h3, ← h4]
    linarith
  · rintro ⟨h0, h1, h3, h4, h5⟩
    rw [Network.qssPower, ← h3, ← h4] at h5
    refine ⟨h0, by rw [h0, h1]; ring, by rw [h5, h1]; ring, h3, h4⟩

/-- A VSM + power filter on the line read about a selected angle `δ*`. -/
structure Model where
  /-- The parameters. -/
  g : VSMLPF
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The operating point `(δ*, 0, P_ref, i_s(δ*))`. -/
def Model.point (m : Model) : State 5 := m.g.qss (Dynamics.mk3 m.δ 0 m.g.Pref)

/-- The field translated so that the operating point is the origin. -/
def Model.field (m : Model) (z : State 5) : State 5 := m.g.field (z + m.point)

/-- The operating point is an equilibrium iff the angle is balanced, `P(δ*) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.field_point_eq_zero_iff (m : Model) (hM : m.g.M ≠ 0)
    (hω : m.g.ωc ≠ 0) (hL : m.g.L ≠ 0) (hZ : m.g.absSq ≠ 0) :
    m.g.field m.point = 0 ↔ m.g.qssPower m.δ = m.g.Pref := by
  rw [m.g.field_eq_zero_iff hM hω hL hZ]
  simp [Model.point, qss]

@[tmio M, powerlib_domain] theorem Model.contDiff_field (m : Model) : ContDiff ℝ 1 m.field :=
  m.g.contDiff_field.comp (contDiff_id.add contDiff_const)

end VSMLPF

/-! ## Power synchronization (pure droop) on the line (three states) -/

/-- Power-synchronization control on the dynamic line: the network, gain `K_p`, set-point
`P_ref`. -/
structure PSC extends Network where
  Kp : ℝ
  Pref : ℝ

namespace PSC

variable (g : PSC)

/-- The closed-loop field on `(δ, i_d, i_q)`. -/
def field (x : State 3) : State 3 :=
  WithLp.toLp 2 ![g.Kp * (g.Pref - g.power (x 0) (x 1) (x 2)), g.rateD (x 0) (x 1) (x 2),
    g.rateQ (x 0) (x 1) (x 2)]

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 3) :
    g.field x 0 = g.Kp * (g.Pref - g.power (x 0) (x 1) (x 2)) := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 3) :
    g.field x 1 = g.rateD (x 0) (x 1) (x 2) := rfl

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 3) :
    g.field x 2 = g.rateQ (x 0) (x 1) (x 2) := rfl

/-- The Jacobian at angle `δ` and current `(i_d, i_q)`; the `(0, 0)` entry is `K_p Q_e`. -/
def jacobian (δ id iq : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![g.Kp * g.reactive δ id iq, -(g.Kp * (g.E * Real.cos δ)), -(g.Kp * (g.E * Real.sin δ));
    -(g.E * Real.sin δ) / g.L, -g.R / g.L, g.X / g.L;
    g.E * Real.cos δ / g.L, -g.X / g.L, -g.R / g.L]

@[tmio M, powerlib_domain] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k g.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [field, Network.power_eq, Network.rateD, Network.rateQ] <;> fun_prop

@[tmio M, powerlib_domain] theorem hasFDerivAt_field (x : State 3) :
    HasFDerivAt g.field
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian (x 0) (x 1) (x 2))) x := by
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![g.Kp • (-((-g.reactive (x 0) (x 1) (x 2)) • coord 0 +
        (g.E * Real.cos (x 0)) • coord 1 + (g.E * Real.sin (x 0)) • coord 2)),
      (-(g.E * Real.sin (x 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 1 + (g.X / g.L) • coord 2,
      (g.E * Real.cos (x 0) / g.L) • coord 0 + (-g.X / g.L) • coord 1 + (-g.R / g.L) • coord 2]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · have h := ((hasFDerivAt_const g.Pref x).sub (g.hasFDerivAt_power 0 1 2 x)).const_smul g.Kp
      convert h using 1
      · funext y; simp
      · ext v; simp
    · exact g.hasFDerivAt_rateD 0 1 2 x
    · exact g.hasFDerivAt_rateQ 0 1 2 x
  · fin_cases i <;> (simp [jacobian, Fin.sum_univ_three]; try ring)

@[tmio M, powerlib_domain] theorem fderiv_field (x : State 3) :
    fderiv ℝ g.field x =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian (x 0) (x 1) (x 2)) :=
  (g.hasFDerivAt_field x).fderiv

/-- The quasi-steady state over `δ`: the current at `i_s(δ)`. -/
def qss (δ : ℝ) : State 3 := WithLp.toLp 2 ![δ, (g.is δ).re, (g.is δ).im]

/-- The reduced (Layer-1) scalar law, *defined* as the angle row of the full field on the
quasi-steady set. -/
def reducedRhs (δ : ℝ) : ℝ := g.field (g.qss δ) 0

/-- The reduced field on `State 1`. -/
def reducedField : State 1 → State 1 := NormalForm.lift g.reducedRhs

/-- The library's quasi-static PSC parameters of the reduced law in the angle `δ − α`:
gain `K_p`, set-point `P_ref − c₀`, maximum power `A`. -/
def toShifted : powerlib.GFM.PSC := ⟨g.Kp, g.Pref - g.c0, g.A⟩

/-- **Quasi-static reduction**: the reduced law is the PSC law `K_p (P* − P_max sin(δ − α))`
with `P* = P_ref − c₀`, `P_max = A`. -/
@[tmio M, powerlib_domain] theorem reducedRhs_eq_shift (hZ : 0 < g.absSq) (δ : ℝ) :
    g.reducedRhs δ = g.toShifted.rhs (δ - g.α) := by
  have hP := g.qssPower_eq_polar hZ δ
  simp only [Network.qssPower] at hP
  show g.Kp * (g.Pref - g.power δ (g.is δ).re (g.is δ).im) =
    g.Kp * (g.Pref - g.c0 - g.A * Real.sin (δ - g.α))
  rw [hP]; ring

/-- **Quasi-static reduction, lossless line**: the reduced field is the quasi-static PSC field
`GFM.PSC ⟨K_p, P_ref, E V/X⟩`. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_psc (hR : g.R = 0) (hX : 0 < g.X) :
    g.reducedField = (⟨g.Kp, g.Pref, g.E * g.V / g.X⟩ : powerlib.GFM.PSC).field := by
  have hZ : 0 < g.absSq := by unfold Network.absSq; positivity
  have h : g.reducedRhs = (⟨g.Kp, g.Pref, g.E * g.V / g.X⟩ : powerlib.GFM.PSC).rhs := by
    funext δ
    rw [g.reducedRhs_eq_shift hZ, Network.α_of_lossless hR hX, sub_zero]
    simp [toShifted, powerlib.GFM.PSC.rhs, Network.c0_of_lossless hR, Network.A_of_lossless hR hX]
  rw [reducedField, h]; rfl

/-- Equilibria: the current at `i_s(δ)` and power balance `P(δ) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hK : g.Kp ≠ 0) (hL : g.L ≠ 0)
    (hZ : g.absSq ≠ 0) (x : State 3) :
    g.field x = 0 ↔ x 1 = (g.is (x 0)).re ∧ x 2 = (g.is (x 0)).im ∧ g.qssPower (x 0) = g.Pref := by
  have hrow : g.field x = 0 ↔ g.field x 0 = 0 ∧ (g.field x 1 = 0 ∧ g.field x 2 = 0) := by
    constructor
    · intro h; simp [h]
    · rintro ⟨h0, h1, h2⟩
      ext i; fin_cases i
      exacts [h0, h1, h2]
  rw [hrow, field_apply_one, field_apply_two, g.rate_eq_zero_iff hL hZ, field_apply_zero,
    mul_eq_zero, or_iff_right hK, sub_eq_zero]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    rw [Network.qssPower, ← h1, ← h2]; exact h0.symm
  · rintro ⟨h1, h2, h3⟩
    rw [Network.qssPower, ← h1, ← h2] at h3
    exact ⟨h3.symm, h1, h2⟩

/-- A PSC on the line read about a selected angle `δ*`. -/
structure Model where
  /-- The parameters. -/
  g : PSC
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The operating point `(δ*, i_s(δ*))`. -/
def Model.point (m : Model) : State 3 := m.g.qss m.δ

/-- The field translated so that the operating point is the origin. -/
def Model.field (m : Model) (z : State 3) : State 3 := m.g.field (z + m.point)

/-- The operating point is an equilibrium iff the angle is balanced, `P(δ*) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.field_point_eq_zero_iff (m : Model) (hK : m.g.Kp ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : m.g.absSq ≠ 0) :
    m.g.field m.point = 0 ↔ m.g.qssPower m.δ = m.g.Pref := by
  rw [m.g.field_eq_zero_iff hK hL hZ]
  simp [Model.point, qss]

@[tmio M, powerlib_domain] theorem Model.contDiff_field (m : Model) : ContDiff ℝ 1 m.field :=
  m.g.contDiff_field.comp (contDiff_id.add contDiff_const)

end PSC

end powerlib.GFM.Line
