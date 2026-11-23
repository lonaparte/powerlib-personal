import theorem.Passive.Series

/-! # The parallel RLC element

A parallel conductance–capacitor–inductor element across one node is the triple `(G, C, Γ)` with
`Γ = 1/L` the reciprocal inductance of the shunt inductor (`Γ = 0`: no inductor, the plain G–C
shunt). With voltage `v`, inductor flux `φ` (`φ' = v`) and injected current `i` it obeys
`C v' = i − G v − Γ φ`; its admittance is `G + C s + Γ/s`. It is the dual of the series element
`Passive.SeriesRLC` (`theorem/Passive/Series.lean`): conductance for resistance, capacitance for
inductance, reciprocal inductance for elastance, voltage for current. Every parallel combination
of G, C and L in the library — a DC-link capacitor with its loss conductance, the node of a
network, the filter capacitor or the resistive load at a converter's terminal, the shunt part of
a line's unit length — is a `Passive.ParallelRLC`; a model whose element has no inductor or no
conductance states it as an explicit field (`Γ = 0`, `G = 0`).

Model boundary.
* One lumped parallel G–C–L element; `G`, `C`, `Γ` real (a physical element has `G ≥ 0`, `C > 0`,
  `Γ ≥ 0`); each law states what it needs.
* At a fixed angular frequency `ω` the element is the phasor admittance `G + jB`,
  `B = ωC − Γ/ω` (`susceptance`; `SeriesRLC.impedance_jω` of `toSeries`).
* No rotating frame, controller or interconnection: the dq forms are `theorem/Passive/Dq.lean`,
  networks are `theorem/Grid/`.

Source: the node equation `C v' = i − G v − Γ φ` of a parallel RLC circuit and its phasor
admittance (work-sync `theory/T-impedance-modeling.md`, `theory/T-park-transformation.md` §1.4).

Results.
* `ParallelRLC` (`G`, `C`, `Γ = 1/L`), `admittance` (`G + C s + Γ/s`), `decay` (`G/C`),
  `susceptance` (`ωC − Γ/ω`), the energies `capacitorEnergy` (`C v²/2`), `inductorEnergy`
  (`Γ φ²/2`), `energy`, and the parallel connection `parallel`.
* `toSeries`: the dual series element `(G, C, Γ)`; `admittance_eq_impedance`,
  `toSeries_parallel`: the admittance is its impedance and a parallel connection is the series
  connection of the duals. Every law of the series element holds for the parallel one through
  `toSeries`, with `G, C, Γ, v, i, φ` for `R, L, S, i, v, q` (definitional): the sign of the decay
  rate (`SeriesRLC.decay_pos_iff`, `SeriesRLC.decay_neg_iff`), the admittance without an inductor
  (`SeriesRLC.impedance_of_noCap`, `SeriesRLC.impedance_eq`), `Y(jω) = G + jB`
  (`SeriesRLC.impedance_jω`), resonance `Y(jω) = 0 ↔ G = 0 ∧ B = 0`
  (`SeriesRLC.impedance_jω_eq_zero_iff`), the complex power `V conj(Y(jω) V) = (G − jB)|V|²`
  (`SeriesRLC.mul_conj_impedance_jω_mul`), additivity (`SeriesRLC.series_impedance`,
  `SeriesRLC.series_reactance`), the energy bounds (`SeriesRLC.inductorEnergy_nonneg`,
  `SeriesRLC.inductorEnergy_pos`, `SeriesRLC.capacitorEnergy_nonneg`, `SeriesRLC.energy_nonneg`)
  and the energy balance along the node equation, `i v − G v²` (`SeriesRLC.power_balance`,
  `SeriesRLC.hasDerivAt_energy`); in the dq frame `ParallelRLC.dqAdmittance` is the dq impedance
  of the dual (`theorem/Passive/Dq.lean`).
-/

noncomputable section

namespace powerlib.Passive

/-- A parallel conductance–capacitor–inductor element: conductance `G`, capacitance `C`,
reciprocal inductance `Γ = 1/L` (`Γ = 0`: no inductor); `C v' = i − G v − Γ φ`, `φ' = v`. -/
@[ext] structure ParallelRLC where
  /-- The conductance. -/
  G : ℝ
  /-- The capacitance. -/
  C : ℝ
  /-- The reciprocal inductance `1/L` of the shunt inductor (`0`: no inductor). -/
  Γ : ℝ

namespace ParallelRLC

variable (e : ParallelRLC)

/-- The admittance `G + C s + Γ/s`. -/
def admittance (s : ℂ) : ℂ := e.G + e.C * s + e.Γ / s

/-- The decay rate `G / C` of the voltage of the G–C part. -/
def decay : ℝ := e.G / e.C

/-- The susceptance `ωC − Γ/ω` at the angular frequency `ω`. -/
def susceptance (ω : ℝ) : ℝ := ω * e.C - e.Γ / ω

/-- The electric energy `C v² / 2`. -/
def capacitorEnergy (v : ℝ) : ℝ := e.C * v ^ 2 / 2

/-- The magnetic energy `Γ φ² / 2 = φ²/(2L)` of the shunt inductor at flux `φ`. -/
def inductorEnergy (φ : ℝ) : ℝ := e.Γ * φ ^ 2 / 2

/-- The stored energy at voltage `v` and inductor flux `φ`. -/
def energy (v φ : ℝ) : ℝ := e.capacitorEnergy v + e.inductorEnergy φ

/-- Two elements in parallel: conductances, capacitances and reciprocal inductances add. -/
def parallel (a b : ParallelRLC) : ParallelRLC := ⟨a.G + b.G, a.C + b.C, a.Γ + b.Γ⟩

/-- The dual series element `(G, C, Γ)`: conductance for resistance, capacitance for inductance,
reciprocal inductance for elastance. With voltage and current exchanged (and flux for charge) the
node equation `C v' = i − G v − Γ φ` is its element equation `L i' = v − R i − S q`, and the
admittance, decay rate, susceptance and energies of `e` are the impedance, decay rate, reactance
and energies of `e.toSeries` by definition. -/
def toSeries : SeriesRLC := ⟨e.G, e.C, e.Γ⟩

/-- The admittance is the impedance of the dual series element. -/
@[tmio M, powerlib_domain] theorem admittance_eq_impedance (s : ℂ) :
    e.admittance s = e.toSeries.impedance s := rfl

/-- Elements in parallel are their dual series elements in series. -/
@[tmio M, powerlib_domain] theorem toSeries_parallel (a b : ParallelRLC) :
    (a.parallel b).toSeries = a.toSeries.series b.toSeries := rfl

end ParallelRLC

end powerlib.Passive
