import theorem.Passive.Parallel
import theorem.Passive.Coupled

/-! # The capacitive coupler: two parallel G–C–L elements linked by a mutual capacitance

Two conducting plate pairs whose electric fields overlap, each port a parallel element
`Passive.ParallelRLC` (`theorem/Passive/Parallel.lean`): the port conductance `G_k`, the
self-capacitance `C_k` of the plates and the parallel compensation inductor `Γ_k = 1/L_k`. The
mutual capacitance `Cm` couples them: the plate charges are `q₁ = C₁ v₁ − Cm v₂`,
`q₂ = −Cm v₁ + C₂ v₂`, the symmetric Maxwell capacitance matrix `[[C₁, −Cm], [−Cm, C₂]]` applied to
the port voltages. It is the dual of the coupled windings `Passive.Coupled`
(`theorem/Passive/Coupled.lean`): conductance for resistance, capacitance for inductance,
reciprocal inductance for elastance, voltage for current, and the off-diagonal capacitance `−Cm`
for the mutual inductance `M` (`toCoupled`). The admittance matrix of the coupler is the
impedance matrix of `toCoupled`, so its port relations are the winding relations of `toCoupled`
with voltages and currents exchanged, and the laws of `Passive.Coupled.impedanceMatrix` and
`Passive.Coupled.inputImpedance` apply to the coupler through `toCoupled`.

Model boundary.
* Two lumped ports, each a parallel element `port₁`, `port₂ : Passive.ParallelRLC`
  (`G_k`, self-capacitance `C_k`, reciprocal compensation inductance `Γ_k`), and one real mutual
  capacitance `Cm`; both port currents flow into the network. A physical coupler has
  `C₁, C₂ > 0` and `Cm² ≤ C₁ C₂`; each law states what it needs.
* At a complex frequency `s` the port currents are `i₁ = Y₁(s) v₁ − Cm s v₂`,
  `i₂ = −Cm s v₁ + Y₂(s) v₂` with the port admittances `Y_k(s) = G_k + C_k s + Γ_k / s`: the
  two-port `Grid.TwoPort.Equations (admittanceMatrix s) i₁ i₂ v₁ v₂` of `theorem/Grid/TwoPort.lean`
  with currents and voltages exchanged.
* A lumped linear capacitive coupler with constant parameters: no fringing-field or frequency
  dependence of the capacitances, no plate resistance or plate inductance, no radiation. No
  source, load or converter: the power link is `theorem/WPT/Capacitive.lean`.

Source: the Maxwell capacitance matrix of a two-conductor-pair system and the duality of planar
networks (exchange of series and parallel elements, voltages and currents, impedances and
admittances) of standard circuit theory; the reflected impedance of
`theorem/Passive/Coupled.lean`, read through that duality.

Results.
* `CoupledParallel` (`port₁`, `port₂`, `Cm`), `admittanceMatrix`
  (`[[Y₁(s), −Cm s], [−Cm s, Y₂(s)]]`), `inputAdmittance` (port 2 loaded by the admittance
  `Y_L`), `coupling` (`k = Cm/√(C₁ C₂)`).
* Duality: `toCoupled` (the dual coupled windings `(port₁.toSeries, port₂.toSeries, −Cm)`),
  `admittanceMatrix_eq_impedanceMatrix` (the admittance matrix is the impedance matrix of
  `toCoupled`), `inputAdmittance_eq` (the input admittance is the input impedance of `toCoupled`),
  `toCoupled_coupling` (the coupling coefficient of `toCoupled` is `−k`).
* `inputAdmittance_jω`: the reflected admittance, with port 2 loaded by `Y_L`,
  `Y_in(jω) = Y₁(jω) + (ωCm)²/(Y₂(jω) + Y_L)`, from `Passive.Coupled.inputImpedance_jω` through
  the duality.
-/

noncomputable section

namespace powerlib.Passive

/-- A capacitive coupler: two parallel G–C–L ports and the mutual capacitance `Cm` between their
plates (Maxwell capacitance matrix `[[C₁, −Cm], [−Cm, C₂]]`). -/
@[ext] structure CoupledParallel where
  /-- The primary port: conductance, self-capacitance and parallel compensation inductor. -/
  port₁ : ParallelRLC
  /-- The secondary port: conductance, self-capacitance and parallel compensation inductor. -/
  port₂ : ParallelRLC
  /-- The mutual capacitance. -/
  Cm : ℝ

namespace CoupledParallel

variable (c : CoupledParallel)

/-- The admittance matrix `[[Y₁(s), −Cm s], [−Cm s, Y₂(s)]]` at the complex frequency `s`:
`i₁ = Y₁(s) v₁ − Cm s v₂`, `i₂ = −Cm s v₁ + Y₂(s) v₂`. -/
def admittanceMatrix (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c.port₁.admittance s, -(c.Cm * s); -(c.Cm * s), c.port₂.admittance s]

/-- The input admittance at `s` with port 2 loaded by the admittance `Y_L` (`i₂ = −Y_L v₂`). -/
def inputAdmittance (YL s : ℂ) : ℂ := Grid.TwoPort.inputImpedance (c.admittanceMatrix s) YL

/-- The coupling coefficient `k = Cm/√(C₁ C₂)`. -/
def coupling : ℝ := c.Cm / Real.sqrt (c.port₁.C * c.port₂.C)

/-- The dual coupled windings: the dual series element of each port and the mutual inductance
`−Cm`. With voltages and currents exchanged, the port relations of the coupler are the winding
relations of `c.toCoupled`. -/
def toCoupled : Coupled := ⟨c.port₁.toSeries, c.port₂.toSeries, -c.Cm⟩

/-- The admittance matrix of the coupler is the impedance matrix of the dual coupled windings. -/
@[tmio M, powerlib_domain] theorem admittanceMatrix_eq_impedanceMatrix (s : ℂ) :
    c.admittanceMatrix s = c.toCoupled.impedanceMatrix s := by
  simp only [admittanceMatrix, Coupled.impedanceMatrix, toCoupled, Complex.ofReal_neg, neg_mul]
  rfl

/-- The input admittance of the coupler is the input impedance of the dual coupled windings. -/
@[tmio M, powerlib_domain] theorem inputAdmittance_eq (YL s : ℂ) :
    c.inputAdmittance YL s = c.toCoupled.inputImpedance YL s := by
  rw [inputAdmittance, admittanceMatrix_eq_impedanceMatrix]
  rfl

/-- The coupling coefficient of the dual coupled windings is `−k`. -/
@[tmio M, powerlib_domain] theorem toCoupled_coupling : c.toCoupled.coupling = -c.coupling := by
  rw [Coupled.coupling, coupling, ← neg_div]
  rfl

/-- The reflected admittance: with port 2 loaded by `Y_L`, the input admittance at `s = jω` is
`Y₁(jω) + (ωCm)²/(Y₂(jω) + Y_L)`. -/
@[tmio M, powerlib_domain] theorem inputAdmittance_jω (YL : ℂ) (ω : ℝ) :
    c.inputAdmittance YL (ω * Complex.I) =
      c.port₁.admittance (ω * Complex.I) +
        ((ω * c.Cm : ℝ) : ℂ) ^ 2 / (c.port₂.admittance (ω * Complex.I) + YL) := by
  rw [inputAdmittance_eq, Coupled.inputImpedance_jω]
  show c.port₁.admittance _ + ((ω * -c.Cm : ℝ) : ℂ) ^ 2 / (c.port₂.admittance _ + YL) = _
  rw [mul_neg, Complex.ofReal_neg, neg_sq]

end CoupledParallel

end powerlib.Passive
