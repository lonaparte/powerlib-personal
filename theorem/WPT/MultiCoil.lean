import theorem.WPT.Link

/-! # Relay coils and multiple receivers of a resonant inductive link

Two multi-coil extensions of the two-coil link of `theorem/WPT/Link.lean`, with every coil
resonant at the operating frequency, so that the series capacitors cancel the self-reactances and
only the winding resistances, the loads and the mutual reactances remain. The model of each is its
set of mesh (KVL) equations; the currents, the input impedance, the power balance, the efficiency
and the load powers are derived from them. With nonzero loop resistances a relay chain
(transmitter, relay, receiver) presents the real input resistance `R₁ + a²/(R₂ + b²/(R₃ + R_L))`,
obtained by reflecting the receiver into the relay and the relay into the transmitter, and its
efficiency is the product of the three stage ratios. With several receivers coupled only to the
transmitter, the reflected resistances add, and the ratio of the powers delivered to two loads is
fixed by the receiver parameters alone.

Model boundary.
* Sinusoidal steady state at one angular frequency `ω`, RMS phasors, every coil a series RLC
  branch tuned to resonance at `ω` (its series compensation capacitor cancels its self-reactance:
  the resonant case `X_k(ω) = 0` of `theorem/WPT/Link.lean`). Coil parameters are real: winding
  resistances and mutual reactances `ωM` (`a = ωM₁₂`, `b = ωM₂₃`, `m i = ωM₁ᵢ`); the sign of a
  mutual reactance is the dot convention of `Passive.Coupled`, all mesh currents entering the
  dotted terminals.
* Relay chain `Relay`: transmitter coil 1 (resistance `R₁`) driven by the source voltage `V`,
  relay coil 2 (resistance `R₂`, closed on itself, no load), receiver coil 3 (resistance `R₃`)
  with the load resistor `R_L` (`load`) in series. Couplings `a` between 1 and 2, `b` between 2
  and 3, and none between 1 and 3 (the cross coupling is neglected). Mesh currents `I₁, I₂, I₃`:
  `V = R₁ I₁ + j a I₂`, `0 = j a I₁ + R₂ I₂ + j b I₃`, `0 = j b I₂ + (R₃ + R_L) I₃`
  (`Relay.Solves`).
* Multiple receivers `MultiReceiver N`: one transmitter coil (resistance `R₁`) driven by `V`, and
  receivers indexed by `Fin N`, receiver `i` with winding resistance `R i`, series load resistor
  `RL i` (`load i`) and mutual reactance `m i` to the transmitter. The receivers are not coupled to
  each other. Mesh currents `I₁` and `J i`: `V = R₁ I₁ + Σ i, j m i J i`,
  `0 = j m i I₁ + (R i + RL i) J i` for every `i` (`MultiReceiver.Solves`).
* The structures admit arbitrary real parameters; each law states the positivity or nonvanishing
  it needs. The efficiency is the load power over the real input power `Re(V Ī₁)`
  (`Link.inputPower`).
* Excluded: detuned coils and frequency splitting (one frequency, every self-reactance cancelled),
  the cross coupling between transmitter and receiver of the relay chain and between receivers,
  the inverter, harmonics, rectifiers and battery loads (ideal sinusoidal voltage source, resistive
  loads), transients and control, and every effect outside the linear lumped coil model of
  `theorem/Passive/Coupled.lean` (saturation, skin effect, parasitic capacitance, radiation).

Source: mesh analysis of magnetically coupled resonant coils with the reflected impedance of
`theorem/Passive/Coupled.lean`; relay (domino) resonators (Zhong, Lee and Hui, *IEEE Trans. Ind.
Electron.* 60 (2013) 261–270); simultaneous transfer to several receivers (Kurs, Moffatt and
Soljačić, *Appl. Phys. Lett.* 96 (2010) 044102).

Results.
* The relay chain: `Relay` (`R₁`, `R₂`, `R₃`, `load`, `a`, `b`), `Relay.Solves` (the mesh
  equations), `Relay.reflected₃` (`Z₃ = b²/(R₃ + R_L)`, the receiver reflected into the relay),
  `Relay.reflected₂` (`Z₂ = a²/(R₂ + Z₃)`, relay and receiver reflected into the transmitter),
  `Relay.inputResistance` (`R₁ + Z₂`), `Relay.outputPower` (`R_L |I₃|²`), `Relay.efficiency`
  (load power over real input power).
* Relay currents: `Relay.receiverCurrent_eq` (`I₃ = −j b I₂/(R₃ + R_L)` for `R₃ + R_L ≠ 0`),
  `Relay.relayCurrent_eq` (`I₂ = −j a I₁/(R₂ + Z₃)` for `R₃ + R_L ≠ 0`, `R₂ + Z₃ ≠ 0`).
* Relay input and power: `Relay.input_eq` (`V = (R₁ + Z₂) I₁` for `R₃ + R_L ≠ 0`,
  `R₂ + Z₃ ≠ 0`: a real input impedance),
  `Relay.inputPower_eq` (power balance, for every solution:
  `Re(V Ī₁) = R₁|I₁|² + R₂|I₂|² + (R₃ + R_L)|I₃|²`), `Relay.efficiency_eq` (with `R₂ > 0`,
  `R₃ + R_L > 0` and `I₁ ≠ 0` the efficiency is the product of the stage ratios
  `[Z₂/(R₁ + Z₂)]·[Z₃/(R₂ + Z₃)]·[R_L/(R₃ + R_L)]`).
* Multiple receivers: `MultiReceiver` (`R₁`, `R`, `load`, `m`), `MultiReceiver.Solves` (the mesh
  equations), `MultiReceiver.reflected` (`m i²/(R i + RL i)`), `MultiReceiver.inputResistance`
  (`R₁ + Σ i, m i²/(R i + RL i)`), `MultiReceiver.loadPower` (`RL i |J i|²`).
* Receiver currents and powers: `MultiReceiver.current_eq` (`J i = −j m i I₁/(R i + RL i)` for
  `R i + RL i ≠ 0`), `MultiReceiver.input_eq` (the reflected resistances add:
  `V = (R₁ + Σ i, m i²/(R i + RL i)) I₁` when every receiver loop resistance is nonzero),
  `MultiReceiver.loadPower_eq` (the power to load `i` is `RL i m i² |I₁|²/(R i + RL i)²` for
  `R i + RL i ≠ 0`), `MultiReceiver.loadPower_div_eq` (with `I₁ ≠ 0` and nonzero loop resistances
  of receivers `i` and `k`, the ratio of the powers to loads `i` and `k` is
  `[RL i m i²/(R i + RL i)²]/[RL k m k²/(R k + RL k)²]`), `MultiReceiver.loadPower_div_independent`
  (under the same conditions that ratio is the same for any two solutions: it does not depend on
  the source).
-/

noncomputable section

namespace powerlib.WPT

open ComplexConjugate

/-- A resonant three-coil relay chain: the winding resistances of the transmitter, the relay and
the receiver, the load resistance in series with the receiver, and the mutual reactances
`a = ωM₁₂`, `b = ωM₂₃`. -/
@[ext] structure Relay where
  /-- The transmitter winding resistance `R₁`. -/
  R₁ : ℝ
  /-- The relay winding resistance `R₂`. -/
  R₂ : ℝ
  /-- The receiver winding resistance `R₃`. -/
  R₃ : ℝ
  /-- The load resistance `R_L` in series with the receiver. -/
  load : ℝ
  /-- The mutual reactance `a = ωM₁₂` between transmitter and relay. -/
  a : ℝ
  /-- The mutual reactance `b = ωM₂₃` between relay and receiver. -/
  b : ℝ

namespace Relay

variable (r : Relay)

/-- The mesh equations: `V = R₁ I₁ + j a I₂`, `0 = j a I₁ + R₂ I₂ + j b I₃`,
`0 = j b I₂ + (R₃ + R_L) I₃`. -/
def Solves (V I₁ I₂ I₃ : ℂ) : Prop :=
  V = (r.R₁ : ℂ) * I₁ + (r.a * Complex.I : ℂ) * I₂ ∧
    0 = (r.a * Complex.I : ℂ) * I₁ + (r.R₂ : ℂ) * I₂ + (r.b * Complex.I : ℂ) * I₃ ∧
    0 = (r.b * Complex.I : ℂ) * I₂ + ((r.R₃ + r.load : ℝ) : ℂ) * I₃

/-- The receiver reflected into the relay loop: `Z₃ = b²/(R₃ + R_L)`. -/
def reflected₃ : ℝ := r.b ^ 2 / (r.R₃ + r.load)

/-- The relay and receiver reflected into the transmitter loop: `Z₂ = a²/(R₂ + Z₃)`. -/
def reflected₂ : ℝ := r.a ^ 2 / (r.R₂ + r.reflected₃)

/-- The input resistance `R₁ + Z₂`. -/
def inputResistance : ℝ := r.R₁ + r.reflected₂

/-- The load power `R_L |I₃|²`. -/
def outputPower (I₃ : ℂ) : ℝ := r.load * Complex.normSq I₃

/-- The efficiency: the load power over the real input power `Re(V Ī₁)`. -/
def efficiency (V I₁ I₃ : ℂ) : ℝ := r.outputPower I₃ / Link.inputPower V I₁

/-- The receiver current: `I₃ = −j b I₂/(R₃ + R_L)`. -/
@[tmio M, powerlib_domain] theorem receiverCurrent_eq {V I₁ I₂ I₃ : ℂ} (h : r.Solves V I₁ I₂ I₃)
    (hL : r.R₃ + r.load ≠ 0) :
    I₃ = -((r.b * Complex.I : ℂ) * I₂) / ((r.R₃ + r.load : ℝ) : ℂ) := by
  have hL' : ((r.R₃ + r.load : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [eq_div_iff hL']
  linear_combination -h.2.2

/-- The relay current: `I₂ = −j a I₁/(R₂ + Z₃)`, the receiver reflected into the relay loop as
the resistance `Z₃ = b²/(R₃ + R_L)`. -/
@[tmio M, powerlib_domain] theorem relayCurrent_eq {V I₁ I₂ I₃ : ℂ} (h : r.Solves V I₁ I₂ I₃)
    (hL : r.R₃ + r.load ≠ 0) (h₂ : r.R₂ + r.reflected₃ ≠ 0) :
    I₂ = -((r.a * Complex.I : ℂ) * I₁) / ((r.R₂ + r.reflected₃ : ℝ) : ℂ) := by
  have h3 := r.receiverCurrent_eq h hL
  have h₂' : ((r.R₂ + r.reflected₃ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h₂
  obtain ⟨-, e2, -⟩ := h
  rw [h3] at e2
  rw [eq_div_iff h₂', reflected₃, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow]
  linear_combination -e2 + ((r.b : ℂ) ^ 2 * I₂ / ((r.R₃ + r.load : ℝ) : ℂ)) * Complex.I_sq

/-- The input impedance is the real `R₁ + Z₂`: `V = (R₁ + a²/(R₂ + Z₃)) I₁`. -/
@[tmio M, powerlib_domain] theorem input_eq {V I₁ I₂ I₃ : ℂ} (h : r.Solves V I₁ I₂ I₃)
    (hL : r.R₃ + r.load ≠ 0) (h₂ : r.R₂ + r.reflected₃ ≠ 0) :
    V = (r.inputResistance : ℂ) * I₁ := by
  have h2 := r.relayCurrent_eq h hL h₂
  obtain ⟨e1, -, -⟩ := h
  rw [h2] at e1
  rw [inputResistance, reflected₂, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow]
  linear_combination e1 - ((r.a : ℂ) ^ 2 * I₁ / ((r.R₂ + r.reflected₃ : ℝ) : ℂ)) * Complex.I_sq

/-- Power balance: the real input power is dissipated in the three windings and the load,
`Re(V Ī₁) = R₁|I₁|² + R₂|I₂|² + (R₃ + R_L)|I₃|²`. -/
@[tmio M, powerlib_domain] theorem inputPower_eq {V I₁ I₂ I₃ : ℂ} (h : r.Solves V I₁ I₂ I₃) :
    Link.inputPower V I₁ = r.R₁ * Complex.normSq I₁ + r.R₂ * Complex.normSq I₂ +
      (r.R₃ + r.load) * Complex.normSq I₃ := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2r := congrArg Complex.re h2
  have h2i := congrArg Complex.im h2
  have h3r := congrArg Complex.re h3
  have h3i := congrArg Complex.im h3
  rw [Link.inputPower, h1]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.zero_re, Complex.zero_im] at h2r h2i h3r h3i ⊢
  linear_combination I₂.re * h2r + I₂.im * h2i + I₃.re * h3r + I₃.im * h3i

/-- The efficiency is the product of the three stage ratios
`[Z₂/(R₁ + Z₂)]·[Z₃/(R₂ + Z₃)]·[R_L/(R₃ + R_L)]`, for a positive relay resistance, a positive
receiver loop resistance and a nonzero transmitter current. -/
@[tmio M, powerlib_domain] theorem efficiency_eq {V I₁ I₂ I₃ : ℂ} (h : r.Solves V I₁ I₂ I₃)
    (h₂ : 0 < r.R₂) (hL : 0 < r.R₃ + r.load) (hI₁ : I₁ ≠ 0) :
    r.efficiency V I₁ I₃ = r.reflected₂ / (r.R₁ + r.reflected₂) *
      (r.reflected₃ / (r.R₂ + r.reflected₃)) * (r.load / (r.R₃ + r.load)) := by
  have h₂₃ : 0 < r.R₂ + r.reflected₃ := by
    have : 0 ≤ r.reflected₃ := div_nonneg (sq_nonneg _) hL.le
    linarith
  have hn : Complex.normSq I₁ ≠ 0 := (Complex.normSq_pos.mpr hI₁).ne'
  have hP : Link.inputPower V I₁ = (r.R₁ + r.reflected₂) * Complex.normSq I₁ := by
    rw [Link.inputPower, r.input_eq h hL.ne' h₂₃.ne', mul_assoc, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.ofReal_re, inputResistance]
  have hO : r.outputPower I₃ = r.load * r.b ^ 2 * r.a ^ 2 /
      ((r.R₃ + r.load) ^ 2 * (r.R₂ + r.reflected₃) ^ 2) * Complex.normSq I₁ := by
    rw [outputPower, r.receiverCurrent_eq h hL.ne', r.relayCurrent_eq h hL.ne' h₂₃.ne']
    simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_ofReal]
    field_simp
  rw [efficiency, hO, hP, mul_div_mul_right _ _ hn, mul_assoc, div_mul_eq_mul_div, reflected₂,
    show r.reflected₃ / (r.R₂ + r.reflected₃) =
      r.b ^ 2 / (r.R₃ + r.load) / (r.R₂ + r.reflected₃) from rfl]
  field_simp

end Relay

/-- One transmitter and `N` receivers coupled only to it, all resonant: the transmitter winding
resistance, and for receiver `i` its winding resistance, its series load resistance and its mutual
reactance `ωM₁ᵢ` to the transmitter. -/
@[ext] structure MultiReceiver (N : ℕ) where
  /-- The transmitter winding resistance `R₁`. -/
  R₁ : ℝ
  /-- The winding resistance `R i` of receiver `i`. -/
  R : Fin N → ℝ
  /-- The load resistance `RL i` in series with receiver `i`. -/
  load : Fin N → ℝ
  /-- The mutual reactance `m i = ωM₁ᵢ` between the transmitter and receiver `i`. -/
  m : Fin N → ℝ

namespace MultiReceiver

variable {N : ℕ} (s : MultiReceiver N)

/-- The mesh equations: `V = R₁ I₁ + Σ i, j m i J i` and `0 = j m i I₁ + (R i + RL i) J i` for
every receiver `i`. -/
def Solves (V I₁ : ℂ) (J : Fin N → ℂ) : Prop :=
  V = (s.R₁ : ℂ) * I₁ + ∑ i, (s.m i * Complex.I : ℂ) * J i ∧
    ∀ i, 0 = (s.m i * Complex.I : ℂ) * I₁ + ((s.R i + s.load i : ℝ) : ℂ) * J i

/-- The resistance `m i²/(R i + RL i)` that receiver `i` reflects into the transmitter loop. -/
def reflected (i : Fin N) : ℝ := s.m i ^ 2 / (s.R i + s.load i)

/-- The input resistance `R₁ + Σ i, m i²/(R i + RL i)`. -/
def inputResistance : ℝ := s.R₁ + ∑ i, s.reflected i

/-- The power `RL i |J i|²` delivered to load `i`. -/
def loadPower (J : Fin N → ℂ) (i : Fin N) : ℝ := s.load i * Complex.normSq (J i)

/-- The current of receiver `i`: `J i = −j m i I₁/(R i + RL i)`. -/
@[tmio M, powerlib_domain] theorem current_eq {V I₁ : ℂ} {J : Fin N → ℂ} (h : s.Solves V I₁ J)
    {i : Fin N} (hi : s.R i + s.load i ≠ 0) :
    J i = -((s.m i * Complex.I : ℂ) * I₁) / ((s.R i + s.load i : ℝ) : ℂ) := by
  have hi' : ((s.R i + s.load i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi
  rw [eq_div_iff hi']
  linear_combination -h.2 i

/-- The reflected resistances add: `V = (R₁ + Σ i, m i²/(R i + RL i)) I₁` when every receiver
loop resistance `R i + RL i` is nonzero. -/
@[tmio M, powerlib_domain] theorem input_eq {V I₁ : ℂ} {J : Fin N → ℂ} (h : s.Solves V I₁ J)
    (hR : ∀ i, s.R i + s.load i ≠ 0) : V = (s.inputResistance : ℂ) * I₁ := by
  have hJ : ∀ i, (s.m i * Complex.I : ℂ) * J i = (s.reflected i : ℂ) * I₁ := by
    intro i
    rw [s.current_eq h (hR i), reflected, Complex.ofReal_div, Complex.ofReal_pow]
    linear_combination (-((s.m i : ℂ) ^ 2 * I₁ / ((s.R i + s.load i : ℝ) : ℂ))) * Complex.I_sq
  rw [h.1]
  simp only [hJ]
  rw [← Finset.sum_mul, inputResistance, Complex.ofReal_add, Complex.ofReal_sum]
  ring

/-- The power delivered to load `i` is `RL i m i² |I₁|²/(R i + RL i)²`. -/
@[tmio M, powerlib_domain] theorem loadPower_eq {V I₁ : ℂ} {J : Fin N → ℂ} (h : s.Solves V I₁ J)
    {i : Fin N} (hi : s.R i + s.load i ≠ 0) :
    s.loadPower J i = s.load i * s.m i ^ 2 * Complex.normSq I₁ / (s.R i + s.load i) ^ 2 := by
  rw [loadPower, s.current_eq h hi]
  simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal]
  ring

/-- With a nonzero transmitter current the ratio of the powers delivered to loads `i` and `k` is
`[RL i m i²/(R i + RL i)²]/[RL k m k²/(R k + RL k)²]`. -/
@[tmio M, powerlib_domain] theorem loadPower_div_eq {V I₁ : ℂ} {J : Fin N → ℂ}
    (h : s.Solves V I₁ J) {i k : Fin N} (hi : s.R i + s.load i ≠ 0) (hk : s.R k + s.load k ≠ 0)
    (hI₁ : I₁ ≠ 0) :
    s.loadPower J i / s.loadPower J k =
      (s.load i * s.m i ^ 2 / (s.R i + s.load i) ^ 2) /
        (s.load k * s.m k ^ 2 / (s.R k + s.load k) ^ 2) := by
  have hn : Complex.normSq I₁ ≠ 0 := (Complex.normSq_pos.mpr hI₁).ne'
  have e : ∀ x c : ℝ, x * Complex.normSq I₁ / c = x / c * Complex.normSq I₁ := fun x c => by ring
  rw [s.loadPower_eq h hi, s.loadPower_eq h hk, e (s.load i * s.m i ^ 2),
    e (s.load k * s.m k ^ 2), mul_div_mul_right _ _ hn]

/-- The ratio of the powers delivered to two loads does not depend on the source: it is the same
for any two solutions with a nonzero transmitter current. -/
@[tmio M, powerlib_domain] theorem loadPower_div_independent {V V' I₁ I₁' : ℂ}
    {J J' : Fin N → ℂ} (h : s.Solves V I₁ J) (h' : s.Solves V' I₁' J') {i k : Fin N}
    (hi : s.R i + s.load i ≠ 0) (hk : s.R k + s.load k ≠ 0) (hI₁ : I₁ ≠ 0) (hI₁' : I₁' ≠ 0) :
    s.loadPower J i / s.loadPower J k = s.loadPower J' i / s.loadPower J' k := by
  rw [s.loadPower_div_eq h hi hk hI₁, s.loadPower_div_eq h' hi hk hI₁']

end MultiReceiver

end powerlib.WPT
