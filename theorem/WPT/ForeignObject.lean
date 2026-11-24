import theorem.WPT.Identification

/-! # A foreign object coupled to the transmitter of the inductive link

A conducting foreign object (a coin, a key, a metal foil) near the transmitter coil of an inductive
power link carries eddy currents. Its eddy-current path is modelled as one closed conducting loop
of impedance `Z_f = R_f + jX_f` (a series branch `(R_f, L_f, S_f)` closed on itself; an untuned
metal object has no capacitor, `S_f = 0`, and `X_f = ωL_f > 0`), coupled to the transmitter coil
only, with the mutual reactance `m_f = ωM_f`, and added to the two-coil link of
`theorem/WPT/Link.lean`. The object current is `I_f = −j m_f I₁/Z_f`; the object reflects the
impedance `m_f²/Z_f` into the primary, so that the input impedance is that of the object-free link
plus `m_f²/Z_f`. The object dissipates `R_f‖I_f‖² = m_f² R_f ‖I₁‖²/(R_f² + X_f²) =
Re(m_f²/Z_f) ‖I₁‖²`, the real input power is shared between the two windings, the load and the
object, and the efficiency is the object-free efficiency `η₀` of `Link.efficiency_eq` times the
fraction of the input power the object does not take; that fraction depends on the impedances
only, not on the source.

With both coils resonant the object-free input impedance is real, and the object adds
`m_f²/Z_f`, of imaginary part `−m_f² X_f/(R_f² + X_f²)`: the resonant input impedance is nonreal
exactly when the object is coupled (`m_f ≠ 0`) and reactive (`X_f ≠ 0`), and for an eddy-current
loop (`X_f > 0`) its imaginary part is negative. A nonreal resonant input impedance flags a
reactive object. A purely resistive object (`X_f = 0`) is not flagged: its reflected resistance
`m_f²/R_f` adds to the reflected resistance `(ωM)²/(R₂ + R_L)` of the secondary, and the resonant
input impedance is exactly that of the object-free link with the load `R_L'`,
`(ωM)²/(R₂ + R_L') = (ωM)²/(R₂ + R_L) + m_f²/R_f` (`ωM ≠ 0`), smaller than `R_L` when `R_f > 0`,
`m_f ≠ 0` and `R₂ + R_L > 0`. One resonant value cannot separate a resistive object from a load
change: the non-identifiability of `theorem/WPT/Identification.lean` extends from `(M, R_L)` to
foreign objects, and the object is read as the identification candidate `(M, R_L')`.

Model boundary.
* The link `link : Link` of `theorem/WPT/Link.lean` (coil pair `(R₁, L₁, S₁)`, `(R₂, L₂, S₂)`,
  mutual inductance `M`, load resistance `R_L` in series with the secondary, angular frequency
  `ω`), and the foreign object as one closed loop `object : Passive.SeriesRLC` (`R_f`, `L_f`,
  `S_f`), of impedance `Z_f = Z_f(jω) = R_f + jX_f(ω)`, coupled to the transmitter coil by the
  mutual inductance `M_f` (`Mf`), `m_f = ωM_f`. The coupling between the object and the
  secondary (receiver) coil is neglected; the sign of `M_f` is the dot convention of
  `Passive.Coupled`.
* Sinusoidal steady state, RMS phasors: the source voltage `V`, the coil currents `I₁`, `I₂` and
  the object current `I_f` satisfy the mesh equations `V = Z₁ I₁ + jωM I₂ + j m_f I_f`,
  `0 = jωM I₁ + (Z₂ + R_L) I₂`, `0 = j m_f I₁ + Z_f I_f` (`Circuit.Solves`): the link equations
  `Link.Solves` with the voltage `j m_f I_f` induced by the object in the primary, and the object
  loop closed on itself.
* The object is one equivalent eddy-current loop with constant lumped parameters: the spatial
  distribution of the eddy currents, the frequency dependence of `R_f` (skin depth), heating and
  the change of `R_f` with temperature are not modelled. A ferromagnetic object that changes the
  self-inductances of the coils enters only through a different coil pair, not as a loop. Ideal
  sinusoidal voltage source and resistive load (the boundary of `theorem/WPT/Link.lean`).
* The detection statements concern exact input-impedance values: no measurement noise, tolerance,
  detection threshold, measurement record or I–O relation. Each law states the nonvanishing or
  positivity it needs (`Z_f ≠ 0`, `R_f ≥ 0`, positive winding resistances).

Source: foreign object detection in inductive power transfer from the change of the
primary-side electrical quantities (Zhang, Yan, Zhu, Li and Mi, *eTransportation* 1 (2019)
100002, a review); the coupled-loop (transformer) model of the eddy currents in a conducting
object, as in eddy-current testing; the reflected impedance of `theorem/Passive/Coupled.lean`
(`Passive.Coupled.inputImpedance_jω`), the link and its efficiency of `theorem/WPT/Link.lean`
(`Link.inputPower_eq`, `Link.efficiency_eq`, `Link.inputImpedance_resonant`), and the
identification candidates of `theorem/WPT/Identification.lean`.

Results.
* The model: `Circuit` (`link`, `object`, `Mf`), `Circuit.Zf` (`Z_f(jω)`), `Circuit.mf`
  (`m_f = ωM_f`), `Circuit.Solves` (the three mesh equations), `Circuit.reflected` (`m_f²/Z_f`),
  `Circuit.inputImpedance` (the object-free input impedance plus `m_f²/Z_f`), `Circuit.objectLoss`
  (`R_f‖I_f‖²`), `Circuit.efficiency` (load power over real input power), `Circuit.apparentLoad`
  (`R_L' = a/(a/(R₂ + R_L) + m_f²/R_f) − R₂`, `a = (ωM)²`).
* Currents and impedance: `Circuit.solves_iff` (the mesh equations written out),
  `Circuit.objectCurrent_eq` (`I_f = −j m_f I₁/Z_f` for `Z_f ≠ 0`), `Circuit.input_eq`
  (`V = Z_in I₁` for `Z_f ≠ 0`, `Z₂ + R_L ≠ 0`), `Circuit.inputImpedance_eq`
  (`Z_in = Z₁ + (ωM)²/(Z₂ + R_L) + m_f²/Z_f`), `Circuit.reflected_re`
  (`Re(m_f²/Z_f) = m_f² R_f/(R_f² + X_f²)`), `Circuit.reflected_im`
  (`Im(m_f²/Z_f) = −m_f² X_f/(R_f² + X_f²)`).
* Power: `Circuit.objectLoss_eq` (`R_f‖I_f‖² = m_f² R_f ‖I₁‖²/(R_f² + X_f²)` for `Z_f ≠ 0`),
  `Circuit.objectLoss_eq_reflected` (`R_f‖I_f‖² = Re(m_f²/Z_f)‖I₁‖²`), `Circuit.inputPower_eq`
  (power balance for every solution, tuned or not:
  `Re(V Ī₁) = R₁‖I₁‖² + (R₂ + R_L)‖I₂‖² + R_f‖I_f‖²`), `Circuit.efficiency_eq` (with
  `R₁ > 0`, `R₂ + R_L > 0`, `R_f ≥ 0`, `I₁ ≠ 0`: `η = η₀ (1 − R_f‖I_f‖²/Re(V Ī₁))`, `η₀` the
  object-free efficiency `Link.eta`), `Circuit.objectLoss_div_inputPower` (the fraction of the
  input power taken by the object is `Re(m_f²/Z_f)/Re Z_in`, for `Z_f ≠ 0`, `Z₂ + R_L ≠ 0`,
  `I₁ ≠ 0`).
* Detection at resonance (`X₁(ω) = X₂(ω) = 0`): `Circuit.inputImpedance_resonant`
  (`Z_in = R₁ + (ωM)²/(R₂ + R_L) + m_f²/Z_f`), `Circuit.inputImpedance_resonant_im`
  (`Im Z_in = −m_f² X_f/(R_f² + X_f²)`), `Circuit.inputImpedance_resonant_im_ne_zero_iff`
  (`Im Z_in ≠ 0 ↔ m_f ≠ 0 ∧ X_f ≠ 0`), `Circuit.inputImpedance_resonant_im_neg` (`m_f ≠ 0`,
  `X_f > 0`: `Im Z_in < 0`).
* A resistive object read as a load change: `Circuit.reflected_apparentLoad`
  (`(ωM)²/(R₂ + R_L') = (ωM)²/(R₂ + R_L) + m_f²/R_f` for `ωM ≠ 0`), `Circuit.apparentLoad_lt`
  (`R_L' < R_L` for `R₂ + R_L > 0`, `R_f > 0`, `m_f ≠ 0`, `ωM ≠ 0`),
  `Circuit.inputImpedance_eq_apparentLoad` (resonant coils, `X_f = 0`, `ωM ≠ 0`: the input impedance
  with the object equals the object-free input impedance of the coil pair with the load `R_L'`),
  `Circuit.inputImpedance_eq_candidate` (the link `ssLink w R_L ω₀` of
  `theorem/WPT/Compensation.lean`, `X_f(ω₀) = 0`, `ω₀ ≠ 0`, `M ≠ 0`: the input impedance at `ω₀`
  with the object is that of the identification candidate `(M, R_L')`,
  `Identification.Candidate.inputImpedance`).
-/

noncomputable section

namespace powerlib.WPT.ForeignObject

open Complex ComplexConjugate

/-- The two-coil link with a foreign object: the link, the eddy-current loop of the object and the
mutual inductance between the transmitter coil and the object. -/
@[ext] structure Circuit where
  /-- The two-coil link: coil pair, load resistance and angular frequency. -/
  link : Link
  /-- The eddy-current loop of the foreign object, a series branch `(R_f, L_f, S_f)` closed on
  itself. -/
  object : Passive.SeriesRLC
  /-- The mutual inductance `M_f` between the transmitter coil and the object. -/
  Mf : ℝ

namespace Circuit

variable (c : Circuit)

/-- The impedance `Z_f(jω) = R_f + jX_f(ω)` of the object loop. -/
abbrev Zf : ℂ := c.object.impedance (c.link.freq * I)

/-- The mutual reactance `m_f = ωM_f` between the transmitter coil and the object. -/
abbrev mf : ℝ := c.link.freq * c.Mf

/-- The mesh equations: the link equations with the voltage `j m_f I_f` the object induces in the
primary, `V = Z₁ I₁ + jωM I₂ + j m_f I_f`, `0 = jωM I₁ + (Z₂ + R_L) I₂`, and the object loop closed
on itself, `0 = j m_f I₁ + Z_f I_f`. -/
def Solves (V I₁ I₂ If : ℂ) : Prop :=
  c.link.Solves (V - (c.mf * I : ℂ) * If) I₁ I₂ ∧ 0 = (c.mf * I : ℂ) * I₁ + c.Zf * If

/-- The impedance `m_f²/Z_f` the object reflects into the primary. -/
def reflected : ℂ := (c.mf : ℂ) ^ 2 / c.Zf

/-- The input impedance with the object: the input impedance of the object-free link, the
secondary terminated by the load, plus `m_f²/Z_f`. -/
def inputImpedance : ℂ :=
  c.link.coils.inputImpedance c.link.load (c.link.freq * I) + c.reflected

/-- The power `R_f ‖I_f‖²` dissipated in the object. -/
def objectLoss (If : ℂ) : ℝ := c.object.R * normSq If

/-- The efficiency: the load power `R_L ‖I₂‖²` over the real input power `Re(V Ī₁)`. -/
def efficiency (V I₁ I₂ : ℂ) : ℝ := c.link.outputPower I₂ / Link.inputPower V I₁

/-- The apparent load `R_L' = a/(a/(R₂ + R_L) + m_f²/R_f) − R₂`, `a = (ωM)²`: the load whose
reflected resistance `a/(R₂ + R_L')` is that of the secondary and a resistive object together. -/
def apparentLoad : ℝ :=
  c.link.mutualReactance ^ 2 / (c.link.mutualReactance ^ 2 /
    (c.link.coils.secondary.R + c.link.load) + c.mf ^ 2 / c.object.R) - c.link.coils.secondary.R

/-! ## Currents and the input impedance -/

/-- The mesh equations written out: `V = Z₁ I₁ + jωM I₂ + j m_f I_f`,
`−R_L I₂ = jωM I₁ + Z₂ I₂`, `0 = j m_f I₁ + Z_f I_f`. -/
@[tmio M, powerlib_domain] theorem solves_iff (V I₁ I₂ If : ℂ) :
    c.Solves V I₁ I₂ If ↔
      V = c.link.Z₁ * I₁ + (c.link.mutualReactance * I : ℂ) * I₂ + (c.mf * I : ℂ) * If ∧
        -(c.link.load * I₂) = (c.link.mutualReactance * I : ℂ) * I₁ + c.link.Z₂ * I₂ ∧
        0 = (c.mf * I : ℂ) * I₁ + c.Zf * If := by
  rw [Solves, Link.solves_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by linear_combination h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by linear_combination h1, h2⟩, h3⟩

/-- The object current: `I_f = −j m_f I₁/Z_f`. -/
@[tmio M, powerlib_domain] theorem objectCurrent_eq {V I₁ I₂ If : ℂ} (h : c.Solves V I₁ I₂ If)
    (hf : c.Zf ≠ 0) : If = -((c.mf * I : ℂ) * I₁) / c.Zf := by
  rw [eq_div_iff hf]
  linear_combination -h.2

/-- The reflected impedance of the object adds to the input impedance of the link:
`V = (Z_in⁰ + m_f²/Z_f) I₁`, `Z_in⁰` the input impedance of the object-free link. -/
@[tmio M, powerlib_domain] theorem input_eq {V I₁ I₂ If : ℂ} (h : c.Solves V I₁ I₂ If)
    (hf : c.Zf ≠ 0) (hZ : c.link.Z₂ + c.link.load ≠ 0) : V = c.inputImpedance * I₁ := by
  have h1 : V - (c.mf * I : ℂ) * If =
      c.link.coils.inputImpedance c.link.load (c.link.freq * I) * I₁ :=
    Grid.TwoPort.terminated_input h.1 (by simpa [Passive.Coupled.impedanceMatrix] using hZ)
  rw [c.objectCurrent_eq h hf] at h1
  rw [inputImpedance, reflected]
  linear_combination h1 - ((c.mf : ℂ) ^ 2 * I₁ / c.Zf) * I_sq

/-- The input impedance with the object, written out:
`Z_in = Z₁(jω) + (ωM)²/(Z₂(jω) + R_L) + m_f²/Z_f(jω)`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_eq :
    c.inputImpedance = c.link.Z₁ + ((c.link.mutualReactance : ℝ) : ℂ) ^ 2 /
      (c.link.Z₂ + c.link.load) + (c.mf : ℂ) ^ 2 / c.Zf := by
  rw [inputImpedance, reflected, Passive.Coupled.inputImpedance_jω]

/-- `Re(m_f²/Z_f) = m_f² R_f/(R_f² + X_f²)`. -/
@[tmio M, powerlib_domain] theorem reflected_re :
    c.reflected.re = c.mf ^ 2 * c.object.R /
      (c.object.R ^ 2 + c.object.reactance c.link.freq ^ 2) := by
  rw [reflected, Zf, Passive.SeriesRLC.impedance_jω, ← ofReal_pow]
  simp only [Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `Im(m_f²/Z_f) = −m_f² X_f/(R_f² + X_f²)`. -/
@[tmio M, powerlib_domain] theorem reflected_im :
    c.reflected.im = -(c.mf ^ 2 * c.object.reactance c.link.freq /
      (c.object.R ^ 2 + c.object.reactance c.link.freq ^ 2)) := by
  rw [reflected, Zf, Passive.SeriesRLC.impedance_jω, ← ofReal_pow]
  simp only [Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-! ## The power taken by the object -/

/-- The object loss: `R_f ‖I_f‖² = m_f² R_f ‖I₁‖²/(R_f² + X_f²)`. -/
@[tmio M, powerlib_domain] theorem objectLoss_eq {V I₁ I₂ If : ℂ} (h : c.Solves V I₁ I₂ If)
    (hf : c.Zf ≠ 0) :
    c.objectLoss If = c.mf ^ 2 * c.object.R * normSq I₁ /
      (c.object.R ^ 2 + c.object.reactance c.link.freq ^ 2) := by
  rw [objectLoss, c.objectCurrent_eq h hf, normSq_div, normSq_neg, normSq_mul, normSq_mul,
    normSq_ofReal, normSq_I, Zf, Passive.SeriesRLC.impedance_jω, normSq_add_mul_I]
  ring

/-- The object loss is the real part of the reflected impedance times the primary current
squared: `R_f ‖I_f‖² = Re(m_f²/Z_f) ‖I₁‖²`. -/
@[tmio M, powerlib_domain] theorem objectLoss_eq_reflected {V I₁ I₂ If : ℂ}
    (h : c.Solves V I₁ I₂ If) (hf : c.Zf ≠ 0) :
    c.objectLoss If = c.reflected.re * normSq I₁ := by
  rw [c.objectLoss_eq h hf, reflected_re]
  ring

/-- Power balance, for every solution, tuned or not: the real input power is dissipated in the two
windings, the load and the object, `Re(V Ī₁) = R₁‖I₁‖² + (R₂ + R_L)‖I₂‖² + R_f‖I_f‖²`. -/
@[tmio M, powerlib_domain] theorem inputPower_eq {V I₁ I₂ If : ℂ} (h : c.Solves V I₁ I₂ If) :
    Link.inputPower V I₁ = c.link.coils.primary.R * normSq I₁ +
      (c.link.coils.secondary.R + c.link.load) * normSq I₂ + c.objectLoss If := by
  have hl := c.link.inputPower_eq h.1
  have h3 := h.2
  rw [Zf, Passive.SeriesRLC.impedance_jω] at h3
  have h3r := congrArg Complex.re h3
  have h3i := congrArg Complex.im h3
  rw [← hl, objectLoss]
  simp only [Link.inputPower, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, Complex.zero_re,
    Complex.zero_im] at h3r h3i ⊢
  linear_combination If.re * h3r + If.im * h3i

/-- The efficiency with the object is the object-free efficiency `η₀ = Link.eta(R₁, R₂, X₂, (ωM)²,
R_L)` of `Link.efficiency_eq` times the fraction of the input power not taken by the object:
`η = η₀ (1 − R_f‖I_f‖²/Re(V Ī₁))`, for positive `R₁` and `R₂ + R_L`, `R_f ≥ 0` and `I₁ ≠ 0`. -/
@[tmio M, powerlib_domain] theorem efficiency_eq {V I₁ I₂ If : ℂ} (h : c.Solves V I₁ I₂ If)
    (hR₁ : 0 < c.link.coils.primary.R) (hR₂ : 0 < c.link.coils.secondary.R + c.link.load)
    (hRf : 0 ≤ c.object.R) (hI₁ : I₁ ≠ 0) :
    c.efficiency V I₁ I₂ = Link.eta c.link.coils.primary.R c.link.coils.secondary.R
      (c.link.coils.secondary.reactance c.link.freq) (c.link.mutualReactance ^ 2) c.link.load *
        (1 - c.objectLoss If / Link.inputPower V I₁) := by
  have hZ : c.link.Z₂ + c.link.load ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [Link.Z₂, Passive.SeriesRLC.impedance_jω, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re] at this
    linarith
  have hη := c.link.efficiency_eq h.1 hI₁ hZ
  have hl := c.link.inputPower_eq h.1
  have hP := c.inputPower_eq h
  have hn1 : 0 < normSq I₁ := normSq_pos.mpr hI₁
  have hP₀ : 0 < c.link.coils.primary.R * normSq I₁ +
      (c.link.coils.secondary.R + c.link.load) * normSq I₂ := by
    have := mul_pos hR₁ hn1
    have := mul_nonneg hR₂.le (normSq_nonneg I₂)
    linarith
  have hf : 0 ≤ c.objectLoss If := mul_nonneg hRf (normSq_nonneg If)
  rw [← hη, Link.efficiency, efficiency, hl, hP]
  field_simp
  ring

/-- The fraction of the input power taken by the object depends on the impedances only, not on
the source: `R_f‖I_f‖²/Re(V Ī₁) = Re(m_f²/Z_f)/Re Z_in`. -/
@[tmio M, powerlib_domain] theorem objectLoss_div_inputPower {V I₁ I₂ If : ℂ}
    (h : c.Solves V I₁ I₂ If) (hf : c.Zf ≠ 0) (hZ : c.link.Z₂ + c.link.load ≠ 0)
    (hI₁ : I₁ ≠ 0) :
    c.objectLoss If / Link.inputPower V I₁ = c.reflected.re / c.inputImpedance.re := by
  have hP : Link.inputPower V I₁ = c.inputImpedance.re * normSq I₁ := by
    rw [Link.inputPower, c.input_eq h hf hZ, mul_assoc, mul_conj]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [c.objectLoss_eq_reflected h hf, hP, mul_div_mul_right _ _ (normSq_pos.mpr hI₁).ne']

/-! ## Detection at resonance -/

/-- With both coils resonant the input impedance with the object is
`R₁ + (ωM)²/(R₂ + R_L) + m_f²/Z_f`: the real resonant input impedance of the link
(`Link.inputImpedance_resonant`) plus the reflected impedance of the object. -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant
    (hX₁ : c.link.coils.primary.reactance c.link.freq = 0)
    (hX₂ : c.link.coils.secondary.reactance c.link.freq = 0) :
    c.inputImpedance = ((c.link.coils.primary.R + c.link.mutualReactance ^ 2 /
      (c.link.coils.secondary.R + c.link.load) : ℝ) : ℂ) + c.reflected := by
  rw [inputImpedance, c.link.inputImpedance_resonant hX₁ hX₂]

/-- With both coils resonant the imaginary part of the input impedance is that of the object,
`Im Z_in = −m_f² X_f/(R_f² + X_f²)`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant_im
    (hX₁ : c.link.coils.primary.reactance c.link.freq = 0)
    (hX₂ : c.link.coils.secondary.reactance c.link.freq = 0) :
    c.inputImpedance.im = -(c.mf ^ 2 * c.object.reactance c.link.freq /
      (c.object.R ^ 2 + c.object.reactance c.link.freq ^ 2)) := by
  rw [c.inputImpedance_resonant hX₁ hX₂, add_im, ofReal_im, zero_add, reflected_im]

/-- Detection: with both coils resonant the input impedance is nonreal **iff** the object is
coupled (`m_f ≠ 0`) and reactive (`X_f ≠ 0`). -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant_im_ne_zero_iff
    (hX₁ : c.link.coils.primary.reactance c.link.freq = 0)
    (hX₂ : c.link.coils.secondary.reactance c.link.freq = 0) :
    c.inputImpedance.im ≠ 0 ↔ c.mf ≠ 0 ∧ c.object.reactance c.link.freq ≠ 0 := by
  rw [c.inputImpedance_resonant_im hX₁ hX₂, neg_ne_zero]
  constructor
  · intro h
    obtain ⟨hn, -⟩ := div_ne_zero_iff.mp h
    obtain ⟨hm, hX⟩ := mul_ne_zero_iff.mp hn
    exact ⟨pow_ne_zero_iff two_ne_zero |>.mp hm, hX⟩
  · rintro ⟨hm, hX⟩
    have : 0 < c.object.R ^ 2 + c.object.reactance c.link.freq ^ 2 := by positivity
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hm) hX) this.ne'

/-- An eddy-current object (`X_f > 0`) coupled to the transmitter (`m_f ≠ 0`) gives the resonant
input impedance a negative imaginary part: it lowers the apparent primary inductance. -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant_im_neg
    (hX₁ : c.link.coils.primary.reactance c.link.freq = 0)
    (hX₂ : c.link.coils.secondary.reactance c.link.freq = 0) (hm : c.mf ≠ 0)
    (hX : 0 < c.object.reactance c.link.freq) : c.inputImpedance.im < 0 := by
  rw [c.inputImpedance_resonant_im hX₁ hX₂, neg_lt_zero]
  have : 0 < c.mf ^ 2 := by positivity
  positivity

/-! ## A resistive object read as a load change -/

/-- The apparent load reflects the secondary and the object together:
`(ωM)²/(R₂ + R_L') = (ωM)²/(R₂ + R_L) + m_f²/R_f` for `ωM ≠ 0`. -/
@[tmio M, powerlib_domain] theorem reflected_apparentLoad (hM : c.link.mutualReactance ≠ 0) :
    c.link.mutualReactance ^ 2 / (c.link.coils.secondary.R + c.apparentLoad) =
      c.link.mutualReactance ^ 2 / (c.link.coils.secondary.R + c.link.load) +
        c.mf ^ 2 / c.object.R := by
  rw [apparentLoad, add_sub_cancel, div_div_cancel₀ (pow_ne_zero 2 hM)]

/-- The apparent load is smaller than the load: `R_L' < R_L` for `R₂ + R_L > 0`, `R_f > 0`,
`m_f ≠ 0` and `ωM ≠ 0`. -/
@[tmio M, powerlib_domain] theorem apparentLoad_lt
    (hR : 0 < c.link.coils.secondary.R + c.link.load) (hRf : 0 < c.object.R) (hm : c.mf ≠ 0)
    (hM : c.link.mutualReactance ≠ 0) : c.apparentLoad < c.link.load := by
  have ha : 0 < c.link.mutualReactance ^ 2 := by positivity
  have hμ : 0 < c.mf ^ 2 / c.object.R := by positivity
  have hb : 0 < c.link.mutualReactance ^ 2 / (c.link.coils.secondary.R + c.link.load) := by
    positivity
  have key : c.link.mutualReactance ^ 2 / (c.link.mutualReactance ^ 2 /
      (c.link.coils.secondary.R + c.link.load) + c.mf ^ 2 / c.object.R) <
      c.link.coils.secondary.R + c.link.load := by
    rw [div_lt_iff₀ (by positivity)]
    have e : (c.link.coils.secondary.R + c.link.load) *
        (c.link.mutualReactance ^ 2 / (c.link.coils.secondary.R + c.link.load)) =
        c.link.mutualReactance ^ 2 := by field_simp
    nlinarith
  rw [apparentLoad]
  linarith

/-- A resistive object is read as a load change: with both coils resonant, `X_f = 0` and
`ωM ≠ 0`, the input impedance with the object equals the input impedance of the object-free coil
pair terminated by the apparent load `R_L'`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_eq_apparentLoad
    (hX₁ : c.link.coils.primary.reactance c.link.freq = 0)
    (hX₂ : c.link.coils.secondary.reactance c.link.freq = 0)
    (hXf : c.object.reactance c.link.freq = 0) (hM : c.link.mutualReactance ≠ 0) :
    c.inputImpedance = c.link.coils.inputImpedance c.apparentLoad (c.link.freq * I) := by
  rw [c.inputImpedance_resonant hX₁ hX₂,
    (⟨c.link.coils, c.apparentLoad, c.link.freq⟩ : Link).inputImpedance_resonant hX₁ hX₂]
  change _ = ((c.link.coils.primary.R + c.link.mutualReactance ^ 2 /
    (c.link.coils.secondary.R + c.apparentLoad) : ℝ) : ℂ)
  rw [c.reflected_apparentLoad hM, reflected, Zf, Passive.SeriesRLC.impedance_jω, hXf]
  push_cast
  ring

/-- The foreign object as an identification candidate: for the series–series link
`ssLink w R_L ω₀` (both coils tuned at `ω₀ ≠ 0`, `M ≠ 0`) and an object with `X_f(ω₀) = 0`, the
input impedance at `ω₀` with the object is that of the object-free candidate `(M, R_L')`
of `theorem/WPT/Identification.lean`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_eq_candidate {w : Passive.Coupled} {ω₀ : ℝ}
    (hc : c.link = ssLink w c.link.load ω₀) (hω₀ : ω₀ ≠ 0) (hM : w.M ≠ 0)
    (hXf : c.object.reactance ω₀ = 0) :
    c.inputImpedance =
      (⟨w.M, c.apparentLoad⟩ : Identification.Candidate).inputImpedance w ω₀ ω₀ := by
  obtain ⟨⟨coils, RL, ω⟩, f, Mf⟩ := c
  simp only [ssLink, Link.mk.injEq] at hc
  obtain ⟨rfl, -, rfl⟩ := hc
  exact inputImpedance_eq_apparentLoad _ (tuned_reactance _ _ hω₀) (tuned_reactance _ _ hω₀) hXf
    (mul_ne_zero hω₀ hM)

end Circuit

end powerlib.WPT.ForeignObject
