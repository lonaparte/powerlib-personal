import theorem.WPT.Link
import theorem.Passive.CoupledParallel

/-! # The parallel-compensated capacitive power link in sinusoidal steady state

The plate pair of a capacitive wireless power link, each port a parallel G–C–L element (port
conductance, self-capacitance of the plates and its parallel compensation inductor), the plates
coupled by the mutual capacitance `Cm`, the secondary loaded by a conductance, driven by a
sinusoidal primary current. It is the exact dual of the series–series compensated inductive link
of `theorem/WPT/Link.lean`: currents for voltages, admittances for impedances, the parallel
elements for the series ones and the mutual capacitance `−Cm` for the mutual inductance
(`toLink`, through `Passive.CoupledParallel.toCoupled`). The phasor equations of the capacitive
link are those of its dual inductive link (`solves_iff_toLink`), so the power balance, the
efficiency, its bound and the optimal load are the theorems of `theorem/WPT/Link.lean` applied
to `toLink`, with the port conductances `G₁`, `G₂` for the winding resistances, the secondary
susceptance `B₂` for the secondary reactance and the mutual susceptance `ωCm` for the mutual
reactance `ωM`.

Model boundary.
* A capacitive coupler `coupler : Passive.CoupledParallel` (ports `(G₁, C₁, Γ₁)`,
  `(G₂, C₂, Γ₂)`, `Γ_k = 1/L_k` the parallel compensation inductors, mutual capacitance `Cm`), a
  load conductance `G_L` (`load`) across port 2, one angular frequency `ω` (`freq`). The
  compensation is parallel–parallel; `Γ_k = 0` is an uncompensated port.
* Sinusoidal steady state with RMS phasors: the source current `J`, the primary voltage `V₁` and
  the secondary voltage `V₂` satisfy `J = Y₁(jω) V₁ − jωCm V₂`,
  `0 = −jωCm V₁ + (Y₂(jω) + G_L) V₂` (`Solves`, the terminated two-port
  `Grid.TwoPort.Terminated` of `Passive.CoupledParallel.admittanceMatrix` at `s = jω`).
* The source is an ideal sinusoidal current source: no inverter, harmonics or DC link; the load is
  an ideal conductance: no rectifier, filter or battery. A lumped linear coupler with constant
  parameters (the boundary of `theorem/Passive/CoupledParallel.lean`). Transients, control and
  frequency tracking are excluded.
* The bound and the optimum are stated for positive port conductances, a nonzero mutual
  susceptance `ωCm` and a nonnegative load; the efficiency is the ratio of the load power to the
  real input power.

Source: the duality between inductive and capacitive power transfer (F. Lu, H. Zhang and C. Mi,
"A review on the recent development of capacitive wireless power transfer technology",
*Energies* 10 (2017) 1752); the efficiency, its maximum and the optimal load of the inductive link
in `theorem/WPT/Link.lean`, read through that duality.

Results.
* The model: `Link` (`coupler`, `load`, `freq`), `Solves`, `inputPower` (`Re(J V̄₁)`),
  `outputPower` (`G_L |V₂|²`), `efficiency`, `quality` (`Q = ωC/G`).
* Duality: `toLink` (the dual inductive link), `solves_iff_toLink` (the phasor equations of the
  link are those of `toLink`), `toLink_mutualReactance` (the mutual reactance of `toLink` is
  `−ωCm`), `solves_iff` (the phasor equations written out).
* Power and efficiency: `inputPower_eq` (power balance:
  `Re(J V̄₁) = G₁|V₁|² + (G₂ + G_L)|V₂|²`), `efficiency_eq` (the efficiency of every solution with
  `V₁ ≠ 0` is `WPT.Link.eta G₁ G₂ B₂ (ωCm)² G_L`).
* The optimum at parallel resonance of the secondary (`B₂ = 0`): `efficiency_le_maxEfficiency`
  (the efficiency never exceeds `WPT.Link.maxEfficiency G₁ G₂ (ωCm)²`),
  `efficiency_eq_maxEfficiency_iff` (it reaches it exactly at
  `G_L = WPT.Link.optimalLoad G₁ G₂ (ωCm)²`), `fomSq_eq` (the figure of merit
  `U² = WPT.Link.fomSq G₁ G₂ (ωCm)² = (ωCm)²/(G₁G₂)` is `k² Q₁ Q₂` with the coupling coefficient
  `k = Cm/√(C₁C₂)` and the port quality factors `Q_k = ωC_k/G_k`).
-/

noncomputable section

namespace powerlib.WPT.Capacitive

open ComplexConjugate

/-- A parallel-compensated capacitive link: the coupler, the load conductance and the angular
frequency. -/
@[ext] structure Link where
  /-- The capacitive coupler with its port conductances and parallel compensation inductors. -/
  coupler : Passive.CoupledParallel
  /-- The load conductance `G_L` across port 2. -/
  load : ℝ
  /-- The angular frequency `ω`. -/
  freq : ℝ

namespace Link

variable (l : Link)

/-- The phasor equations: `J = Y₁(jω) V₁ − jωCm V₂`, `−G_L V₂ = −jωCm V₁ + Y₂(jω) V₂`. -/
def Solves (J V₁ V₂ : ℂ) : Prop :=
  Grid.TwoPort.Terminated (l.coupler.admittanceMatrix (l.freq * Complex.I)) l.load J V₁ V₂

/-- The dual inductive link: the dual coupled windings `coupler.toCoupled`, the load conductance
as the load resistance and the same angular frequency. -/
def toLink : WPT.Link := ⟨l.coupler.toCoupled, l.load, l.freq⟩

/-- The real input power `Re(J V̄₁)`. -/
def inputPower (J V₁ : ℂ) : ℝ := (J * conj V₁).re

/-- The load power `G_L |V₂|²`. -/
def outputPower (V₂ : ℂ) : ℝ := l.load * Complex.normSq V₂

/-- The efficiency: the load power over the real input power. -/
def efficiency (J V₁ V₂ : ℂ) : ℝ := l.outputPower V₂ / inputPower J V₁

/-- The quality factor `Q = ωC/G` of a port at `ω`. -/
def quality (ω : ℝ) (e : Passive.ParallelRLC) : ℝ := ω * e.C / e.G

/-! ## Duality -/

/-- The phasor equations of the capacitive link are those of its dual inductive link. -/
@[tmio M, powerlib_domain] theorem solves_iff_toLink (J V₁ V₂ : ℂ) :
    l.Solves J V₁ V₂ ↔ l.toLink.Solves J V₁ V₂ := by
  rw [Solves, Passive.CoupledParallel.admittanceMatrix_eq_impedanceMatrix]
  rfl

/-- The mutual reactance of the dual inductive link is `−ωCm`. -/
@[tmio M, powerlib_domain] theorem toLink_mutualReactance :
    l.toLink.mutualReactance = -(l.freq * l.coupler.Cm) :=
  mul_neg _ _

/-- The phasor equations written out. -/
@[tmio M, powerlib_domain] theorem solves_iff (J V₁ V₂ : ℂ) :
    l.Solves J V₁ V₂ ↔
      J = l.coupler.port₁.admittance (l.freq * Complex.I) * V₁ -
          ((l.freq * l.coupler.Cm : ℝ) : ℂ) * Complex.I * V₂ ∧
        -(l.load * V₂) = -(((l.freq * l.coupler.Cm : ℝ) : ℂ) * Complex.I * V₁) +
          l.coupler.port₂.admittance (l.freq * Complex.I) * V₂ := by
  rw [solves_iff_toLink, WPT.Link.solves_iff, toLink_mutualReactance, Complex.ofReal_neg]
  simp only [neg_mul, ← sub_eq_add_neg]
  exact Iff.rfl

/-! ## Power and efficiency -/

/-- Power balance: the real input power is dissipated in the two port conductances and the load,
`Re(J V̄₁) = G₁|V₁|² + (G₂ + G_L)|V₂|²`. -/
@[tmio M, powerlib_domain] theorem inputPower_eq {J V₁ V₂ : ℂ} (h : l.Solves J V₁ V₂) :
    inputPower J V₁ = l.coupler.port₁.G * Complex.normSq V₁ +
      (l.coupler.port₂.G + l.load) * Complex.normSq V₂ :=
  l.toLink.inputPower_eq ((l.solves_iff_toLink J V₁ V₂).mp h)

/-- The efficiency of every solution with a nonzero primary voltage is `eta` at the port
conductances, the secondary susceptance `B₂` and the squared mutual susceptance `(ωCm)²`: it
depends neither on the primary susceptance nor on the source. -/
@[tmio M, powerlib_domain] theorem efficiency_eq {J V₁ V₂ : ℂ} (h : l.Solves J V₁ V₂)
    (hV₁ : V₁ ≠ 0) (hY : l.coupler.port₂.admittance (l.freq * Complex.I) + l.load ≠ 0) :
    l.efficiency J V₁ V₂ = WPT.Link.eta l.coupler.port₁.G l.coupler.port₂.G
      (l.coupler.port₂.susceptance l.freq) ((l.freq * l.coupler.Cm) ^ 2) l.load := by
  rw [← neg_sq, ← toLink_mutualReactance]
  exact l.toLink.efficiency_eq ((l.solves_iff_toLink J V₁ V₂).mp h) hV₁ hY

/-- At parallel resonance of the secondary (`B₂ = 0`) the loaded secondary admittance is the real
`G₂ + G_L`. -/
@[tmio M, powerlib_domain] private theorem secondary_resonant
    (hB₂ : l.coupler.port₂.susceptance l.freq = 0) :
    l.coupler.port₂.admittance (l.freq * Complex.I) + l.load =
      ((l.coupler.port₂.G + l.load : ℝ) : ℂ) := by
  rw [Passive.ParallelRLC.admittance_eq_impedance, Passive.SeriesRLC.impedance_jω]
  show (l.coupler.port₂.G : ℂ) + (l.coupler.port₂.susceptance l.freq : ℂ) * Complex.I + l.load = _
  rw [hB₂]
  push_cast
  ring

/-- With the secondary at parallel resonance (`B₂ = 0`), positive port conductances, a nonzero
mutual susceptance and a nonnegative load, every solution with a nonzero primary voltage runs at
most at the maximum efficiency `η_max` of `theorem/WPT/Link.lean` at `(G₁, G₂, (ωCm)²)`. -/
@[tmio M, powerlib_domain] theorem efficiency_le_maxEfficiency {J V₁ V₂ : ℂ}
    (h : l.Solves J V₁ V₂) (hV₁ : V₁ ≠ 0) (hB₂ : l.coupler.port₂.susceptance l.freq = 0)
    (hG₁ : 0 < l.coupler.port₁.G) (hG₂ : 0 < l.coupler.port₂.G)
    (hm : l.freq * l.coupler.Cm ≠ 0) (hGL : 0 ≤ l.load) :
    l.efficiency J V₁ V₂ ≤ WPT.Link.maxEfficiency l.coupler.port₁.G l.coupler.port₂.G
      ((l.freq * l.coupler.Cm) ^ 2) := by
  have hY : l.coupler.port₂.admittance (l.freq * Complex.I) + l.load ≠ 0 := by
    rw [l.secondary_resonant hB₂]
    exact_mod_cast (by linarith : l.coupler.port₂.G + l.load ≠ 0)
  rw [l.efficiency_eq h hV₁ hY, hB₂]
  exact WPT.Link.eta_le_maxEfficiency hG₁ hG₂ (by positivity) hGL

/-- With the secondary at parallel resonance (`B₂ = 0`), positive port conductances, a nonzero
mutual susceptance and a nonnegative load, a solution with a nonzero primary voltage reaches the
maximum efficiency exactly at the optimal load conductance `G_L = optimalLoad G₁ G₂ (ωCm)²`. -/
@[tmio M, powerlib_domain] theorem efficiency_eq_maxEfficiency_iff {J V₁ V₂ : ℂ}
    (h : l.Solves J V₁ V₂) (hV₁ : V₁ ≠ 0) (hB₂ : l.coupler.port₂.susceptance l.freq = 0)
    (hG₁ : 0 < l.coupler.port₁.G) (hG₂ : 0 < l.coupler.port₂.G)
    (hm : l.freq * l.coupler.Cm ≠ 0) (hGL : 0 ≤ l.load) :
    l.efficiency J V₁ V₂ = WPT.Link.maxEfficiency l.coupler.port₁.G l.coupler.port₂.G
        ((l.freq * l.coupler.Cm) ^ 2) ↔
      l.load = WPT.Link.optimalLoad l.coupler.port₁.G l.coupler.port₂.G
        ((l.freq * l.coupler.Cm) ^ 2) := by
  have hY : l.coupler.port₂.admittance (l.freq * Complex.I) + l.load ≠ 0 := by
    rw [l.secondary_resonant hB₂]
    exact_mod_cast (by linarith : l.coupler.port₂.G + l.load ≠ 0)
  rw [l.efficiency_eq h hV₁ hY, hB₂]
  exact WPT.Link.eta_eq_maxEfficiency_iff hG₁ hG₂ (by positivity) hGL

/-- The figure of merit of the coupler, `U² = (ωCm)²/(G₁G₂)`, is `k² Q₁ Q₂` with the coupling
coefficient `k = Cm/√(C₁C₂)` and the port quality factors `Q_k = ωC_k/G_k`. -/
@[tmio M, powerlib_domain] theorem fomSq_eq (ω : ℝ) (c : Passive.CoupledParallel)
    (hC : 0 < c.port₁.C * c.port₂.C) (hG₁ : c.port₁.G ≠ 0) (hG₂ : c.port₂.G ≠ 0) :
    WPT.Link.fomSq c.port₁.G c.port₂.G ((ω * c.Cm) ^ 2) =
      c.coupling ^ 2 * quality ω c.port₁ * quality ω c.port₂ := by
  have h := WPT.Link.fomSq_eq ω c.toCoupled hC hG₁ hG₂
  rw [c.toCoupled_coupling, neg_sq] at h
  rw [← neg_sq, ← mul_neg]
  exact h

end Link

end powerlib.WPT.Capacitive
