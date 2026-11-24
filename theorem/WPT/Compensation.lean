import theorem.WPT.Link
import theorem.Passive.Parallel

/-! # Compensation networks of the inductive link: SS, SP and double-sided LCC

The compensation capacitors and inductors that turn the coil pair of `theorem/WPT/Link.lean` into
a resonant link, with the design targets each topology is chosen for. Series–series (SS): the
capacitors synthesized from the coils and the operating frequency, `S_k = ω² L_k`, make the input
impedance real for every load and, with a lossless primary, the output current load-independent.
Series–parallel (SP): with the secondary capacitor across the load resonating the secondary coil
and the primary capacitor resonating the primary leakage inductance `σ L₁`, the input impedance is
the real `R₁ + (M/L₂)² R_L` for every load. Double-sided LCC: with the series inductor, the shunt
capacitor and the compensated coil of each side tuned to one reactance, the primary coil current
is fixed by the source voltage, the output current is fixed by the source voltage, and the input
impedance is real, for every load.

Model boundary.
* The coil pair `Passive.Coupled` with the boundary of `theorem/Passive/Coupled.lean`, one angular
  frequency `ω ≠ 0`, RMS phasors in sinusoidal steady state, an ideal sinusoidal voltage source and
  a resistive load `R_L`; no inverter, rectifier, harmonics, control or transients.
* SS: the link of `theorem/WPT/Link.lean` with the synthesized capacitors (`ssLink`).
* SP: the secondary coil is lossless and uncompensated in series (`R₂ = 0`, `S₂ = 0`); the load
  is the parallel element `Passive.ParallelRLC` `(1/R_L, C₂, 0)` (load resistor in parallel with
  the secondary capacitor), the secondary terminated by its impedance `1/(1/R_L + jωC₂)`.
* Double-sided LCC (`LCC`): source — series inductor `L_f1` — node `A` with the shunt capacitor
  `C_f1 = 1/S_f1` — the primary branch of the coil pair (coil `L₁`, its winding resistance and its
  series capacitor) back to the source; the secondary branch of the pair (coil `L₂`, series
  capacitor, lossless winding `R₂ = 0`) — node `B` with the shunt capacitor `C_f2 = 1/S_f2` —
  series inductor `L_f2` — load `R_L`. Phasor unknowns: the source current `I_in`, the coil
  currents `I₁`, `I₂` (into the dotted terminals of the pair), the output current `I_o`, the node
  voltages `V_A`, `V_B` (`LCC.Solves`). Tuning (`LCC.Tuned`): on each side the series inductor, the
  shunt capacitor and the compensated coil have one reactance `X_k`: `ωL_fk = S_fk/ω = X_k(ω)`.

Source: SS and SP compensation and the primary capacitance `1/(ω²(L₁ − M²/L₂))` of SP (Wang, Covic
and Stielau, *IEEE Trans. Ind. Electron.* 51 (2004) 148–157); the double-sided LCC network and its
tuning (Li, Li, Deng, Nguyen and Mi, *IEEE Trans. Veh. Technol.* 64 (2015) 2261–2273); the review
of compensation topologies (Zhang and Mi, *IEEE Trans. Veh. Technol.* 65 (2016) 4768–4778).

Results.
* Tuning: `tunedElastance` (`S = ω² L`); `tuned_reactance` (a branch with the synthesized
  elastance is resonant, through `Passive.SeriesRLC.reactance_eq_zero_iff`).
* SS: `tunedCoils` (the coil pair with both capacitors synthesized to resonate at `ω₀`), `ssLink`
  (the tuned pair operated at its resonance),
  `ssLink_inputImpedance` (the input impedance is the real `R₁ + (ωM)²/(R₂ + R_L)` for every load:
  zero phase angle), `ssLink_secondaryCurrent` (with lossless coils the output current is
  `−jV/(ωM)` for every load), `ssLink_efficiency_le` (the efficiency of every operating point is at
  most `η_max`, `theorem/WPT/Link.lean`).
* SP: `spLoad` (the load in parallel with the secondary capacitor), `spPrimaryElastance`
  (`ω² σ L₁`), `sp_inputImpedance` (with the secondary capacitor resonating `L₂` and the primary
  capacitor resonating `σ L₁`, the input impedance is the real `R₁ + (M/L₂)² R_L` for every load).
* Double-sided LCC: `LCC`, `LCC.Solves`, `LCC.Tuned`; `LCC.primaryCurrent_eq` (the primary coil
  current is `−jV/X₁`, fixed by the source), `LCC.outputCurrent_eq` (the output current is
  `−j ωM V/(X₁X₂)`, fixed by the source: a load-independent current output),
  `LCC.inputCurrent_eq` (the source current is `V (R₁/X₁² + (ωM)² R_L/(X₁X₂)²)`, in phase with `V`:
  zero phase angle for every load and every primary winding resistance).
-/

noncomputable section

namespace powerlib.WPT

open Complex

/-- The elastance `S = ω² L` that resonates the inductance `L` at `ω`. -/
def tunedElastance (L ω : ℝ) : ℝ := ω ^ 2 * L

/-- A branch with the synthesized elastance is resonant at `ω`. -/
@[tmio M, powerlib_domain] theorem tuned_reactance (R L : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    (⟨R, L, tunedElastance L ω⟩ : Passive.SeriesRLC).reactance ω = 0 :=
  (Passive.SeriesRLC.reactance_eq_zero_iff hω).mpr rfl

/-! ## Series–series compensation -/

/-- The coil pair with both series capacitors synthesized to resonate its coils at `ω₀`. -/
def tunedCoils (w : Passive.Coupled) (ω₀ : ℝ) : Passive.Coupled :=
  ⟨⟨w.primary.R, w.primary.L, tunedElastance w.primary.L ω₀⟩,
    ⟨w.secondary.R, w.secondary.L, tunedElastance w.secondary.L ω₀⟩, w.M⟩

/-- The SS link: the coil pair tuned at the operating frequency `ω`. -/
def ssLink (w : Passive.Coupled) (RL ω : ℝ) : Link := ⟨tunedCoils w ω, RL, ω⟩

/-- The SS link has a real input impedance `R₁ + (ωM)²/(R₂ + R_L)` for every load. -/
@[tmio M, powerlib_domain] theorem ssLink_inputImpedance (w : Passive.Coupled) (RL : ℝ) {ω : ℝ}
    (hω : ω ≠ 0) :
    (ssLink w RL ω).coils.inputImpedance RL (ω * I) =
      ((w.primary.R + (ω * w.M) ^ 2 / (w.secondary.R + RL) : ℝ) : ℂ) :=
  (ssLink w RL ω).inputImpedance_resonant (tuned_reactance _ _ hω) (tuned_reactance _ _ hω)

/-- With lossless coils the SS link has the output current `−jV/(ωM)` for every load. -/
@[tmio M, powerlib_domain] theorem ssLink_secondaryCurrent (w : Passive.Coupled) (RL : ℝ) {ω : ℝ}
    (hω : ω ≠ 0) (hR₁ : w.primary.R = 0) (hM : ω * w.M ≠ 0) {V I₁ I₂ : ℂ}
    (h : (ssLink w RL ω).Solves V I₁ I₂) : I₂ = -(I * V) / ((ω * w.M : ℝ) : ℂ) := by
  refine (ssLink w RL ω).secondaryCurrent_of_lossless_primary h ?_ hM
  rw [Link.Z₁, Passive.SeriesRLC.impedance_jω]
  simp only [ssLink, tunedCoils]
  rw [tuned_reactance _ _ hω, hR₁]
  simp

/-- Every operating point of the SS link with lossy coils and a nonzero primary current runs at
most at the maximum efficiency `η_max` of the coil pair. -/
@[tmio M, powerlib_domain] theorem ssLink_efficiency_le (w : Passive.Coupled) {RL ω : ℝ}
    (hω : ω ≠ 0) (hR₁ : 0 < w.primary.R) (hR₂ : 0 < w.secondary.R) (hM : ω * w.M ≠ 0)
    (hRL : 0 ≤ RL) {V I₁ I₂ : ℂ} (h : (ssLink w RL ω).Solves V I₁ I₂) (hI₁ : I₁ ≠ 0) :
    (ssLink w RL ω).efficiency V I₁ I₂ ≤
      Link.maxEfficiency w.primary.R w.secondary.R ((ω * w.M) ^ 2) := by
  have hX := tuned_reactance w.secondary.R w.secondary.L hω
  have hZ : (ssLink w RL ω).Z₂ + RL ≠ 0 := by
    rw [Link.Z₂, Passive.SeriesRLC.impedance_jω]
    simp only [ssLink, tunedCoils]
    rw [hX]
    push_cast
    simp only [zero_mul, add_zero]
    exact_mod_cast (by linarith : w.secondary.R + RL ≠ 0)
  rw [(ssLink w RL ω).efficiency_eq h hI₁ hZ]
  simp only [ssLink, tunedCoils]
  rw [hX]
  exact Link.eta_le_maxEfficiency hR₁ hR₂ (by positivity) hRL

/-! ## Series–parallel compensation -/

/-- The SP load: the load resistor `R_L` in parallel with the secondary capacitor `C₂`. -/
def spLoad (RL C₂ : ℝ) : Passive.ParallelRLC := ⟨1 / RL, C₂, 0⟩

/-- The SP primary elastance `ω² σ L₁ = ω² (L₁ − M²/L₂)`: the primary capacitor resonates the
primary leakage inductance. -/
def spPrimaryElastance (w : Passive.Coupled) (ω : ℝ) : ℝ := ω ^ 2 * (w.leakage * w.primary.L)

/-- The parallel load as an impedance: with `ω² L₂ C₂ = 1`,
`(1/R + jωC₂)⁻¹ = R x/(x + jR)`, `x = ωL₂`. -/
@[tmio T, powerlib_foundation] private theorem sp_loadImpedance {R C₂ ω L₂ : ℝ} (hR : 0 < R)
    (hx : ω * L₂ ≠ 0) (hC : ω ^ 2 * L₂ * C₂ = 1) :
    ((1 / R : ℝ) + (C₂ : ℂ) * (ω * I))⁻¹ = (R * (ω * L₂) : ℂ) / ((ω * L₂ : ℂ) + R * I) := by
  have hx' : (ω * L₂ : ℂ) ≠ 0 := by exact_mod_cast hx
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hC' : (ω : ℂ) ^ 2 * L₂ * C₂ = 1 := by exact_mod_cast hC
  rw [inv_eq_iff_eq_inv, inv_div, eq_div_iff (mul_ne_zero hR' hx')]
  push_cast
  field_simp
  linear_combination (R * I) * hC'

/-- The secondary branch with the parallel load: `jx + R x/(x + jR) = j x²/(x + jR)`. -/
@[tmio T, powerlib_foundation] private theorem sp_secondaryImpedance {R x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * I + (R * x : ℂ) / ((x : ℂ) + R * I) = (x : ℂ) ^ 2 * I / ((x : ℂ) + R * I) := by
  have hd : (x : ℂ) + R * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact hx this
  rw [eq_div_iff hd, add_mul, div_mul_cancel₀ _ hd]
  linear_combination (R * x : ℂ) * I_sq

/-- The reflected impedance of the SP secondary: `(ωM)²/(j x²/(x + jR)) = (M/L₂)² R − j ωM²/L₂`
with `x = ωL₂`. -/
@[tmio T, powerlib_foundation] private theorem sp_reflected {R L₂ ω M : ℝ} (hL₂ : L₂ ≠ 0)
    (hω : ω ≠ 0) :
    ((ω * M : ℝ) : ℂ) ^ 2 / (((ω * L₂ : ℝ) : ℂ) ^ 2 * I / (((ω * L₂ : ℝ) : ℂ) + R * I)) =
      ((M / L₂) ^ 2 * R : ℝ) - (ω * M ^ 2 / L₂ : ℝ) * I := by
  have hx : ω * L₂ ≠ 0 := mul_ne_zero hω hL₂
  have hd : ((ω * L₂ : ℝ) : ℂ) + R * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact hx (mul_eq_zero.mpr this)
  have hL' : (L₂ : ℂ) ≠ 0 := by exact_mod_cast hL₂
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  rw [div_div_eq_mul_div, div_eq_iff (by simp [hω', hL', I_ne_zero])]
  push_cast
  field_simp
  linear_combination (-(ω:ℂ) ^ 3 * M ^ 2 * L₂ ^ 2 * (↑ω * ↑L₂ + ↑R * I) * (ω * L₂ * I) +
    (M ^ 2 * ω * L₂ + M ^ 2 * ω ^ 4 * L₂ ^ 3 * R * I ^ 2 + M ^ 2 * ω ^ 5 * L₂ ^ 4 * I)) * I_sq

/-- SP compensation: with a lossless uncompensated secondary coil, the secondary capacitor across
the load resonating `L₂` (`ω² L₂ C₂ = 1`) and the primary capacitor resonating `σ L₁`, the input
impedance is the real `R₁ + (M/L₂)² R_L` for every load. -/
@[tmio M, powerlib_domain] theorem sp_inputImpedance (w : Passive.Coupled) {RL C₂ ω : ℝ}
    (hω : ω ≠ 0) (hL₁ : w.primary.L ≠ 0) (hL₂ : w.secondary.L ≠ 0) (hRL : 0 < RL)
    (hR₂ : w.secondary.R = 0) (hS₂ : w.secondary.S = 0) (hS₁ : w.primary.S = spPrimaryElastance w ω)
    (hC : ω ^ 2 * w.secondary.L * C₂ = 1) :
    w.inputImpedance ((spLoad RL C₂).admittance (ω * I))⁻¹ (ω * I) =
      ((w.primary.R + (w.M / w.secondary.L) ^ 2 * RL : ℝ) : ℂ) := by
  have hx : ω * w.secondary.L ≠ 0 := mul_ne_zero hω hL₂
  have hY : (spLoad RL C₂).admittance (ω * I) = ((1 / RL : ℝ) : ℂ) + (C₂ : ℂ) * (ω * I) := by
    simp [spLoad, Passive.ParallelRLC.admittance]
  have hX₁ : w.primary.reactance ω = ω * w.M ^ 2 / w.secondary.L := by
    rw [Passive.SeriesRLC.reactance, hS₁, spPrimaryElastance, Passive.Coupled.leakage]
    field_simp
    ring
  have hX₂ : w.secondary.reactance ω = ω * w.secondary.L := by
    rw [Passive.SeriesRLC.reactance, hS₂, zero_div, sub_zero]
  rw [Passive.Coupled.inputImpedance_jω, Passive.SeriesRLC.impedance_jω,
    Passive.SeriesRLC.impedance_jω, hX₁, hX₂, hR₂, hY, sp_loadImpedance hRL hx hC]
  push_cast
  rw [zero_add, show (RL : ℂ) * (ω * w.secondary.L) = ((RL * (ω * w.secondary.L) : ℝ) : ℂ) by
      push_cast; ring,
    show (ω : ℂ) * w.secondary.L = ((ω * w.secondary.L : ℝ) : ℂ) by push_cast; ring,
    show ((RL * (ω * w.secondary.L) : ℝ) : ℂ) = (RL : ℂ) * ((ω * w.secondary.L : ℝ) : ℂ) by
      push_cast; ring,
    sp_secondaryImpedance hx]
  rw [show ((ω : ℂ) * w.M) ^ 2 = ((ω * w.M : ℝ) : ℂ) ^ 2 by push_cast; ring, sp_reflected hL₂ hω]
  push_cast
  ring

/-! ## Double-sided LCC compensation -/

/-- The double-sided LCC link: the coil pair (each branch the coil, its winding resistance and its
series capacitor), the series inductors `L_f1`, `L_f2`, the shunt elastances `S_f1 = 1/C_f1`,
`S_f2 = 1/C_f2`, the load and the angular frequency. -/
@[ext] structure LCC where
  /-- The coil pair with the series capacitors of the coils. -/
  coils : Passive.Coupled
  /-- The primary series inductor `L_f1`. -/
  Lf₁ : ℝ
  /-- The primary shunt elastance `S_f1 = 1/C_f1`. -/
  Sf₁ : ℝ
  /-- The secondary series inductor `L_f2`. -/
  Lf₂ : ℝ
  /-- The secondary shunt elastance `S_f2 = 1/C_f2`. -/
  Sf₂ : ℝ
  /-- The load resistance. -/
  load : ℝ
  /-- The angular frequency. -/
  freq : ℝ

namespace LCC

variable (c : LCC)

/-- The phasor equations: the source loop through `L_f1`, the shunt capacitor at `A`, the coil pair
between the nodes `A` and `B`, the shunt capacitor at `B` and the load loop through `L_f2`. -/
def Solves (V Iin I₁ I₂ Io VA VB : ℂ) : Prop :=
  V = c.Lf₁ * (c.freq * I) * Iin + VA ∧
    c.freq * I * VA = c.Sf₁ * (Iin - I₁) ∧
    Grid.TwoPort.Equations (c.coils.impedanceMatrix (c.freq * I)) VA VB I₁ I₂ ∧
    c.freq * I * VB = c.Sf₂ * (-I₂ - Io) ∧
    VB = (c.Lf₂ * (c.freq * I) + c.load) * Io

/-- Tuning: on each side the series inductor, the shunt capacitor and the compensated coil have the
one reactance `X_k` at `ω`: `ωL_fk = S_fk/ω = X_k(ω)`. -/
def Tuned (X₁ X₂ : ℝ) : Prop :=
  c.freq * c.Lf₁ = X₁ ∧ c.Sf₁ = c.freq * X₁ ∧ c.coils.primary.reactance c.freq = X₁ ∧
    c.freq * c.Lf₂ = X₂ ∧ c.Sf₂ = c.freq * X₂ ∧ c.coils.secondary.reactance c.freq = X₂

/-- The tuned design from the coil pair, the frequency and the two compensation reactances:
`L_fk = X_k/ω`, `S_fk = ω X_k` and the coil capacitors `S_k = ω(ωL_k − X_k)`. -/
def design (w : Passive.Coupled) (X₁ X₂ RL ω : ℝ) : LCC :=
  ⟨⟨⟨w.primary.R, w.primary.L, ω * (ω * w.primary.L - X₁)⟩,
    ⟨w.secondary.R, w.secondary.L, ω * (ω * w.secondary.L - X₂)⟩, w.M⟩,
    X₁ / ω, ω * X₁, X₂ / ω, ω * X₂, RL, ω⟩

/-- The design is tuned. -/
@[tmio M, powerlib_domain] theorem design_tuned (w : Passive.Coupled) (X₁ X₂ RL : ℝ) {ω : ℝ}
    (hω : ω ≠ 0) : (design w X₁ X₂ RL ω).Tuned X₁ X₂ := by
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_⟩ <;>
    simp only [design, Passive.SeriesRLC.reactance] <;> field_simp <;> ring

/-- The primary coil current is fixed by the source: `I₁ = −jV/X₁`, whatever the secondary and the
load. -/
@[tmio M, powerlib_domain] theorem primaryCurrent_eq {X₁ X₂ : ℝ} (ht : c.Tuned X₁ X₂)
    (hω : c.freq ≠ 0) (hX₁ : X₁ ≠ 0) {V Iin I₁ I₂ Io VA VB : ℂ}
    (h : c.Solves V Iin I₁ I₂ Io VA VB) : I₁ = -(I * V) / X₁ := by
  have t1' : (c.freq : ℂ) * c.Lf₁ = X₁ := by exact_mod_cast ht.1
  have t2' : (c.Sf₁ : ℂ) = c.freq * X₁ := by exact_mod_cast ht.2.1
  have hω' : (c.freq : ℂ) ≠ 0 := by exact_mod_cast hω
  have hX' : (X₁ : ℂ) ≠ 0 := by exact_mod_cast hX₁
  have key : (c.freq : ℂ) * (X₁ * I₁ + I * V) = 0 := by
    linear_combination (c.freq * I) * h.1 + h.2.1 + (c.freq ^ 2 * c.Lf₁ * Iin) * I_sq +
      (Iin - I₁) * t2' - (c.freq * Iin) * t1'
  rw [eq_div_iff hX']
  linear_combination (mul_eq_zero.mp key).resolve_left hω'

/-- The secondary node relation: `X₂ I_o = ωM I₁` with a lossless secondary winding. -/
@[tmio M, powerlib_domain] private theorem outputCurrent_of_primary {X₁ X₂ : ℝ}
    (ht : c.Tuned X₁ X₂) (hω : c.freq ≠ 0) (hX₂ : X₂ ≠ 0) (hR₂ : c.coils.secondary.R = 0)
    {V Iin I₁ I₂ Io VA VB : ℂ} (h : c.Solves V Iin I₁ I₂ Io VA VB) :
    Io = (c.freq * c.coils.M : ℝ) * I₁ / X₂ := by
  have t2' : (c.Sf₂ : ℂ) = c.freq * X₂ := by exact_mod_cast ht.2.2.2.2.1
  have hω' : (c.freq : ℂ) ≠ 0 := by exact_mod_cast hω
  have hX' : (X₂ : ℂ) ≠ 0 := by exact_mod_cast hX₂
  have h4 := h.2.2.1.2
  simp only [Passive.Coupled.impedanceMatrix, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Passive.SeriesRLC.impedance_jω, ht.2.2.2.2.2, hR₂, Complex.ofReal_zero, zero_add] at h4
  have key : (c.freq : ℂ) * (X₂ * Io - c.freq * c.coils.M * I₁) = 0 := by
    linear_combination (-(c.freq : ℂ) * I) * h4 + h.2.2.2.1 +
      (-c.freq ^ 2 * c.coils.M * I₁ - c.freq * X₂ * I₂) * I_sq + (-I₂ - Io) * t2'
  rw [eq_div_iff hX']
  push_cast
  linear_combination (mul_eq_zero.mp key).resolve_left hω'

/-- The output current is fixed by the source: `I_o = −j ωM V/(X₁X₂)`, a load-independent current
output (lossless secondary winding). -/
@[tmio M, powerlib_domain] theorem outputCurrent_eq {X₁ X₂ : ℝ} (ht : c.Tuned X₁ X₂)
    (hω : c.freq ≠ 0) (hX₁ : X₁ ≠ 0) (hX₂ : X₂ ≠ 0) (hR₂ : c.coils.secondary.R = 0)
    {V Iin I₁ I₂ Io VA VB : ℂ} (h : c.Solves V Iin I₁ I₂ Io VA VB) :
    Io = -(I * (c.freq * c.coils.M : ℝ) * V) / (X₁ * X₂ : ℝ) := by
  have hX₁' : (X₁ : ℂ) ≠ 0 := by exact_mod_cast hX₁
  have hX₂' : (X₂ : ℂ) ≠ 0 := by exact_mod_cast hX₂
  rw [c.outputCurrent_of_primary ht hω hX₂ hR₂ h, c.primaryCurrent_eq ht hω hX₁ h]
  push_cast
  field_simp

/-- The source current is in phase with the source voltage:
`I_in = V (R₁/X₁² + (ωM)² R_L/(X₁X₂)²)`, zero phase angle for every load and every primary winding
resistance (lossless secondary winding). -/
@[tmio M, powerlib_domain] theorem inputCurrent_eq {X₁ X₂ : ℝ} (ht : c.Tuned X₁ X₂)
    (hω : c.freq ≠ 0) (hX₁ : X₁ ≠ 0) (hX₂ : X₂ ≠ 0) (hR₂ : c.coils.secondary.R = 0)
    {V Iin I₁ I₂ Io VA VB : ℂ} (h : c.Solves V Iin I₁ I₂ Io VA VB) :
    Iin = ((c.coils.primary.R / X₁ ^ 2 +
      (c.freq * c.coils.M) ^ 2 * c.load / (X₁ * X₂) ^ 2 : ℝ) : ℂ) * V := by
  have hω' : (c.freq : ℂ) ≠ 0 := by exact_mod_cast hω
  have hX₁' : (X₁ : ℂ) ≠ 0 := by exact_mod_cast hX₁
  have hX₂' : (X₂ : ℂ) ≠ 0 := by exact_mod_cast hX₂
  have t2' : (c.Sf₁ : ℂ) = c.freq * X₁ := by exact_mod_cast ht.2.1
  have s1' : (c.freq : ℂ) * c.Lf₂ = X₂ := by exact_mod_cast ht.2.2.2.1
  have s2' : (c.Sf₂ : ℂ) = c.freq * X₂ := by exact_mod_cast ht.2.2.2.2.1
  have h3 := h.2.2.1.1
  simp only [Passive.Coupled.impedanceMatrix, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Passive.SeriesRLC.impedance_jω, ht.2.2.1] at h3
  -- the source current from the node `A` and the coil pair
  have kin : (c.freq : ℂ) * (X₁ * Iin - (I * c.coils.primary.R * I₁ -
      c.freq * c.coils.M * I₂)) = 0 := by
    linear_combination -h.2.1 + (c.freq * I) * h3 - (Iin - I₁) * t2' +
      (c.freq * X₁ * I₁ + c.freq ^ 2 * c.coils.M * I₂) * I_sq
  -- the secondary coil current from the node `B` and the load loop
  have k2 : (c.freq : ℂ) * (X₂ * I₂ + I * c.load * Io) = 0 := by
    linear_combination h.2.2.2.1 - (c.freq * I) * h.2.2.2.2 - (I₂ + Io) * s2' +
      (c.freq * Io) * s1' - (c.freq ^ 2 * c.Lf₂ * Io) * I_sq
  have hin := (mul_eq_zero.mp kin).resolve_left hω'
  have h2 := (mul_eq_zero.mp k2).resolve_left hω'
  have hI₁ := c.primaryCurrent_eq ht hω hX₁ h
  have hIo := c.outputCurrent_eq ht hω hX₁ hX₂ hR₂ h
  have hI₂ : I₂ = -(I * c.load * Io) / X₂ := by
    rw [eq_div_iff hX₂']
    linear_combination h2
  have hIin : Iin = (I * c.coils.primary.R * I₁ - c.freq * c.coils.M * I₂) / X₁ := by
    rw [eq_div_iff hX₁']
    linear_combination hin
  rw [hIin, hI₂, hIo, hI₁]
  push_cast
  field_simp
  linear_combination (-V * (c.coils.primary.R * X₂ ^ 2 + c.freq ^ 2 * c.coils.M ^ 2 * c.load)) *
    I_sq

end LCC

end powerlib.WPT
