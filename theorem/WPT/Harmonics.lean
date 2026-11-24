import theorem.WPT.CurrentLimits

/-! # Harmonics of the bridge voltages in the lossless resonant link

The bridges of a resonant inductive link impose periodic, non-sinusoidal voltages (square or
quasi-square waves). The coil pair is linear and time-invariant, so it responds harmonic by
harmonic: the `n`-th harmonic phasors of the bridge voltages and of the coil currents satisfy the
two-port equations of the pair at the frequency `nω`, `CurrentLimits.Driven w (n ω) V₁ V₂ I₁ I₂`.
This module solves these equations exactly for the lossless link tuned at the fundamental `ω`.

At `nω` a coil tuned at `ω` (`S = ω²L`) is no longer resonant: its reactance is
`X(nω) = ωL(n² − 1)/n` (`reactance_harmonic`), inductive for `n ≥ 2`. With `a = ωL₁(n² − 1)/n`,
`b = nωM`, `c = ωL₂(n² − 1)/n` the harmonic equations read `V₁ = j(a I₁ + b I₂)`,
`V₂ = j(b I₁ + c I₂)`, and with `δ = ac − b² ≠ 0` their unique solution is
`I₁ = −j(c V₁ − b V₂)/δ`, `I₂ = −j(a V₂ − b V₁)/δ`. The harmonic power the primary bridge
delivers is `Re(V₁ Ī₁) = b Im(V₁ V̄₂)/δ`, and the secondary bridge receives exactly that power
(`Re(V₂ Ī₂) = −Re(V₁ Ī₁)`): the coils are lossless. Here
`δ = (ω²/n²)((n² − 1)² L₁L₂ − n⁴M²)`; at `n = 1`, `a = c = 0`, `b = ωM`, `δ = −(ωM)²` and the
formulas are the gyrator law of `CurrentLimits.currents_lossless`. For a given `n ≥ 1`, `δ > 0`
iff `n⁴M² < (n² − 1)²L₁L₂`, and `δ > 0` for every `n ≥ 3` iff `81M² < 64L₁L₂`, a coupling
coefficient `|k| < 8/9` (the binding harmonic is `n = 3`, since `(n² − 1)/n² ≥ 8/9`).

Bounds per harmonic. A square or quasi-square bridge voltage of level `V_dc` has `n`-th harmonic
amplitude at most `(4V_dc/π)/n` (`SpecialFunctions.squareWave_harmonic`,
`SpecialFunctions.quasiSquareWave_harmonic_le` of `theorem/SpecialFunctions/Harmonics.lean`), so
with `ρ_k = 4V_dc,k/π`, the square-wave fundamental (peak; `2√2 V_dc,k/π` for RMS phasors), the
harmonic phasors satisfy `‖V_k‖ ≤ ρ_k/n`. Then the harmonic power is at most
`|ωM|ρ₁ρ₂/(n|δ|)`, which for `δ > 0` is the fraction `nM²/((n² − 1)²L₁L₂ − n⁴M²)` of the
fundamental limit `ρ₁ρ₂/|ωM|` (`CurrentLimits.power_le`), and the harmonic currents are at most
`‖I₁‖ ≤ (|c|ρ₁ + |b|ρ₂)/(n|δ|)`, `‖I₂‖ ≤ (|b|ρ₁ + |a|ρ₂)/(n|δ|)`. Both bridges of a square or
quasi-square drive have only odd harmonics; the statements hold for every `n ≠ 0`.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`), linear and
  time-invariant, with lossless windings `R₁ = R₂ = 0`, both coils tuned at the fundamental
  angular frequency `ω ≠ 0` (`X₁(ω) = X₂(ω) = 0`, so `S_k = ω²L_k`). The harmonic index is
  `n : ℕ`, `n ≠ 0`.
* At each harmonic: the phasors `V₁`, `V₂` of the `n`-th harmonic of the two bridge voltages and
  `I₁`, `I₂` of the coil currents (into the dotted terminals), related by
  `CurrentLimits.Driven w (n ω)`, the two-port equations of the impedance matrix at `jnω`. That the
  periodic steady state is the superposition of these harmonic responses is the modelling premise
  of this module, not a theorem of it; the time-domain totals (RMS currents, total transferred
  power, capacitor and device stresses) are the Parseval sums of the harmonic terms over all `n`
  (`theorem/SpecialFunctions/Parseval.lean`); the sums are bounded in closed form in
  `theorem/WPT/HarmonicTotals.lean`.
* The bridges are ideal voltage sources of the given waveforms: no switching transients, dead-time
  commutation, device drops or DC-link ripple. The bound `‖V_k‖ ≤ ρ_k/n` is a hypothesis; its
  reading for square and quasi-square waves comes from the generic module cited above. Winding
  and core losses, the frequency dependence of the coil parameters (skin and proximity effect,
  self-resonance) and the harmonic losses are not modelled.

Source: the harmonic (Fourier) analysis of resonant converters driven by square-wave bridges,
beyond the fundamental-harmonic approximation (Steigerwald, *IEEE Trans. Power Electron.* 3
(1988) 174–182, for the fundamental-harmonic picture that this module extends); the two-port
equations `CurrentLimits.Driven` of `theorem/WPT/CurrentLimits.lean`, the series RLC reactance of
`theorem/Passive/Series.lean` and the harmonics of the bridge waveforms of
`theorem/SpecialFunctions/Harmonics.lean`.

Results.
* `harmonicReactance L ω n` (`ωL(n² − 1)/n`), `determinant w ω n`
  (`δ = a c − b²` with `a = harmonicReactance L₁ ω n`, `b = nωM`, `c = harmonicReactance L₂ ω n`).
* `reactance_harmonic`: a coil tuned at `ω ≠ 0` has `X(nω) = ωL(n² − 1)/n` for `n ≠ 0`.
* `driven_iff`: for the lossless link tuned at `ω`, `Driven w (nω)` iff `V₁ = j(a I₁ + b I₂)` and
  `V₂ = j(b I₁ + c I₂)`.
* `currents_eq`: with `δ ≠ 0`, `I₁ = −j(c V₁ − b V₂)/δ`, `I₂ = −j(a V₂ − b V₁)/δ`;
  `driven_currents`: these currents solve the harmonic equations for every `V₁`, `V₂`.
* `power₁_eq` (`Re(V₁ Ī₁) = b Im(V₁ V̄₂)/δ`), `power₂_eq` (`Re(V₂ Ī₂) = −b Im(V₁ V̄₂)/δ`).
* `determinant_eq` (`δ = (ω²/n²)((n² − 1)²L₁L₂ − n⁴M²)` for `n ≠ 0`), `determinant_one`
  (`δ = −(ωM)²` at `n = 1`: the gyrator), `harmonicReactance_one` (`a = c = 0` at `n = 1`),
  `determinant_pos_iff` (`0 < δ ↔ n⁴M² < (n² − 1)²L₁L₂`, `ω ≠ 0`, `n ≠ 0`),
  `forall_determinant_pos_iff` (`δ > 0` for every `n ≥ 3` iff `81M² < 64L₁L₂`, `ω ≠ 0`).
* Bounds with `‖V_k‖ ≤ ρ_k/n` and `δ ≠ 0`: `abs_power_le` (`|Re(V₁ Ī₁)| ≤ |ωM|ρ₁ρ₂/(n|δ|)`),
  `abs_power_le_fundamental` (if `n⁴M² < (n² − 1)²L₁L₂`:
  `|Re(V₁ Ī₁)| ≤ nM²/((n² − 1)²L₁L₂ − n⁴M²) · ρ₁ρ₂/|ωM|`), `norm_current₁_le`
  (`‖I₁‖ ≤ (|c|ρ₁ + |b|ρ₂)/(n|δ|)`), `norm_current₂_le` (`‖I₂‖ ≤ (|b|ρ₁ + |a|ρ₂)/(n|δ|)`).
-/

noncomputable section

namespace powerlib.WPT.Harmonics

open Complex ComplexConjugate

/-- The reactance `ωL(n² − 1)/n` at the harmonic `nω` of a coil of inductance `L` tuned at `ω`. -/
def harmonicReactance (L ω : ℝ) (n : ℕ) : ℝ := ω * L * ((n : ℝ) ^ 2 - 1) / n

/-- The determinant `δ = a c − b²` of the lossless link tuned at `ω`, at the harmonic `nω`:
`a = ωL₁(n² − 1)/n`, `b = nωM`, `c = ωL₂(n² − 1)/n`. -/
def determinant (w : Passive.Coupled) (ω : ℝ) (n : ℕ) : ℝ :=
  harmonicReactance w.primary.L ω n * harmonicReactance w.secondary.L ω n - (n * ω * w.M) ^ 2

variable {w : Passive.Coupled} {ω : ℝ} {n : ℕ}

/-- A coil tuned at `ω ≠ 0` (`S = ω²L`) has the reactance `ωL(n² − 1)/n` at `nω`. -/
@[tmio M, powerlib_domain] theorem reactance_harmonic {b : Passive.SeriesRLC} (hω : ω ≠ 0)
    (hX : b.reactance ω = 0) (hn : n ≠ 0) :
    b.reactance (n * ω) = harmonicReactance b.L ω n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Passive.SeriesRLC.reactance, (Passive.SeriesRLC.reactance_eq_zero_iff hω).mp hX,
    harmonicReactance]
  field_simp

/-- At `n = 1` the tuned coil is resonant: `a = c = 0`. -/
@[tmio M, powerlib_domain] theorem harmonicReactance_one (L ω : ℝ) :
    harmonicReactance L ω 1 = 0 := by
  simp [harmonicReactance]

/-- The harmonic equations of the lossless link tuned at `ω`:
`V₁ = j(a I₁ + b I₂)`, `V₂ = j(b I₁ + c I₂)`. -/
@[tmio M, powerlib_domain] theorem driven_iff (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hn : n ≠ 0) (V₁ V₂ I₁ I₂ : ℂ) :
    CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂ ↔
      V₁ = I * ((harmonicReactance w.primary.L ω n : ℂ) * I₁ + ((n * ω * w.M : ℝ) : ℂ) * I₂) ∧
        V₂ = I * (((n * ω * w.M : ℝ) : ℂ) * I₁ +
          (harmonicReactance w.secondary.L ω n : ℂ) * I₂) := by
  rw [CurrentLimits.driven_iff, reactance_harmonic hω hX₁ hn, reactance_harmonic hω hX₂ hn, hR₁,
    hR₂, Complex.ofReal_zero, zero_add, zero_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩

/-- The exact harmonic currents: with `δ ≠ 0`, `I₁ = −j(c V₁ − b V₂)/δ`,
`I₂ = −j(a V₂ − b V₁)/δ`. -/
@[tmio M, powerlib_domain] theorem currents_eq {V₁ V₂ I₁ I₂ : ℂ} (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) :
    I₁ = -(I * ((harmonicReactance w.secondary.L ω n : ℂ) * V₁ - ((n * ω * w.M : ℝ) : ℂ) * V₂)) /
        (determinant w ω n : ℂ) ∧
      I₂ = -(I * ((harmonicReactance w.primary.L ω n : ℂ) * V₂ - ((n * ω * w.M : ℝ) : ℂ) * V₁)) /
        (determinant w ω n : ℂ) := by
  obtain ⟨h1, h2⟩ := (driven_iff hω hX₁ hX₂ hR₁ hR₂ hn V₁ V₂ I₁ I₂).mp h
  have hδ' : (determinant w ω n : ℂ) ≠ 0 := by exact_mod_cast hδ
  have hD : (determinant w ω n : ℂ) = (harmonicReactance w.primary.L ω n : ℂ) *
      (harmonicReactance w.secondary.L ω n : ℂ) - ((n * ω * w.M : ℝ) : ℂ) ^ 2 := by
    simp only [determinant]
    push_cast
    ring
  set a : ℂ := (harmonicReactance w.primary.L ω n : ℂ)
  set c : ℂ := (harmonicReactance w.secondary.L ω n : ℂ)
  set b : ℂ := ((n * ω * w.M : ℝ) : ℂ)
  constructor
  · rw [eq_div_iff hδ', hD, h1, h2]
    linear_combination ((a * c - b ^ 2) * I₁) * I_sq
  · rw [eq_div_iff hδ', hD, h1, h2]
    linear_combination ((a * c - b ^ 2) * I₂) * I_sq

/-- The currents `−j(c V₁ − b V₂)/δ`, `−j(a V₂ − b V₁)/δ` solve the harmonic equations for every
pair of harmonic bridge phasors (`δ ≠ 0`). -/
@[tmio M, powerlib_domain] theorem driven_currents (V₁ V₂ : ℂ) (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) :
    CurrentLimits.Driven w (n * ω) V₁ V₂
      (-(I * ((harmonicReactance w.secondary.L ω n : ℂ) * V₁ - ((n * ω * w.M : ℝ) : ℂ) * V₂)) /
        (determinant w ω n : ℂ))
      (-(I * ((harmonicReactance w.primary.L ω n : ℂ) * V₂ - ((n * ω * w.M : ℝ) : ℂ) * V₁)) /
        (determinant w ω n : ℂ)) := by
  rw [driven_iff hω hX₁ hX₂ hR₁ hR₂ hn]
  have hδ' : (determinant w ω n : ℂ) ≠ 0 := by exact_mod_cast hδ
  have hD : (determinant w ω n : ℂ) = (harmonicReactance w.primary.L ω n : ℂ) *
      (harmonicReactance w.secondary.L ω n : ℂ) - ((n * ω * w.M : ℝ) : ℂ) ^ 2 := by
    simp only [determinant]
    push_cast
    ring
  set a : ℂ := (harmonicReactance w.primary.L ω n : ℂ)
  set c : ℂ := (harmonicReactance w.secondary.L ω n : ℂ)
  set b : ℂ := ((n * ω * w.M : ℝ) : ℂ)
  set δ : ℂ := (determinant w ω n : ℂ)
  constructor
  · field_simp
    rw [hD]
    linear_combination ((a * c - b ^ 2) * V₁) * I_sq
  · field_simp
    rw [hD]
    linear_combination ((a * c - b ^ 2) * V₂) * I_sq

/-- The harmonic power delivered by the primary bridge: `Re(V₁ Ī₁) = b Im(V₁ V̄₂)/δ`. -/
@[tmio M, powerlib_domain] theorem power₁_eq {V₁ V₂ I₁ I₂ : ℂ} (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re = n * ω * w.M * (V₁ * conj V₂).im / determinant w ω n := by
  rw [(currents_eq hω hX₁ hX₂ hR₁ hR₂ hn hδ h).1, map_div₀, Complex.conj_ofReal, mul_div_assoc',
    Complex.div_ofReal_re]
  congr 1
  simp only [map_neg, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The secondary bridge receives what the primary delivers: `Re(V₂ Ī₂) = −b Im(V₁ V̄₂)/δ`. -/
@[tmio M, powerlib_domain] theorem power₂_eq {V₁ V₂ I₁ I₂ : ℂ} (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) :
    (V₂ * conj I₂).re = -(n * ω * w.M * (V₁ * conj V₂).im / determinant w ω n) := by
  have hb := CurrentLimits.power_balance w (n * ω) h
  rw [hR₁, hR₂, zero_mul, zero_mul, add_zero, power₁_eq hω hX₁ hX₂ hR₁ hR₂ hn hδ h] at hb
  linarith

/-- `δ = (ω²/n²)((n² − 1)²L₁L₂ − n⁴M²)` for `n ≠ 0`. -/
@[tmio M, powerlib_domain] theorem determinant_eq (hn : n ≠ 0) :
    determinant w ω n = ω ^ 2 / (n : ℝ) ^ 2 *
      (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [determinant, harmonicReactance]
  field_simp

/-- At the fundamental, `δ = −(ωM)²`: with `a = c = 0` and `b = ωM` the harmonic formulas are the
gyrator law of the lossless resonant link. -/
@[tmio M, powerlib_domain] theorem determinant_one : determinant w ω 1 = -(ω * w.M) ^ 2 := by
  simp only [determinant, harmonicReactance_one, Nat.cast_one, one_mul, zero_mul, zero_sub]

/-- For a given harmonic `n ≠ 0` and `ω ≠ 0`: `0 < δ ↔ n⁴M² < (n² − 1)²L₁L₂`. -/
@[tmio M, powerlib_domain] theorem determinant_pos_iff (hω : ω ≠ 0) (hn : n ≠ 0) :
    0 < determinant w ω n ↔
      (n : ℝ) ^ 4 * w.M ^ 2 < ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk : 0 < ω ^ 2 / (n : ℝ) ^ 2 := by positivity
  rw [determinant_eq hn, mul_pos_iff_of_pos_left hk, sub_pos]

/-- `δ > 0` at every harmonic `n ≥ 3` iff `81M² < 64L₁L₂` (coupling `|k| < 8/9`): `n = 3` is the
binding harmonic, since `(n² − 1)/n² ≥ 8/9` for `n ≥ 3`. -/
@[tmio M, powerlib_domain] theorem forall_determinant_pos_iff (hω : ω ≠ 0) :
    (∀ n : ℕ, 3 ≤ n → 0 < determinant w ω n) ↔
      81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L) := by
  constructor
  · intro h
    have h3 := (determinant_pos_iff (w := w) hω (by norm_num : (3 : ℕ) ≠ 0)).mp (h 3 le_rfl)
    norm_num at h3
    linarith
  · intro hk m hm
    rw [determinant_pos_iff hω (by omega)]
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    set x : ℝ := (m : ℝ) ^ 2 with hx
    have hx9 : 9 ≤ x := by nlinarith
    have hP : 0 < w.primary.L * w.secondary.L := by nlinarith [sq_nonneg w.M]
    -- `81 (x − 1)² ≥ 64 x²` for `x ≥ 9`
    have hq : 64 * x ^ 2 ≤ 81 * (x - 1) ^ 2 := by nlinarith
    have h4 : (m : ℝ) ^ 4 = x ^ 2 := by rw [hx]; ring
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_right hq hP.le, sq_nonneg x, mul_pos (by positivity : 0 < x ^ 2)
      (by linarith : 0 < 64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2)]

/-! ## Bounds per harmonic -/

/-- With harmonic bridge phasors `‖V_k‖ ≤ ρ_k/n` and `δ ≠ 0`, the harmonic power is at most
`|ωM|ρ₁ρ₂/(n|δ|)`. -/
@[tmio M, powerlib_domain] theorem abs_power_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ} (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁ / n) (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    |(V₁ * conj I₁).re| ≤ |ω * w.M| * ρ₁ * ρ₂ / (n * |determinant w ω n|) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hδa : 0 < |determinant w ω n| := abs_pos.mpr hδ
  have hr₁ : 0 ≤ ρ₁ / n := (norm_nonneg _).trans h₁
  have hb : |(n : ℝ) * ω * w.M| = n * |ω * w.M| := by
    rw [mul_assoc, abs_mul, abs_of_pos hn']
  rw [power₁_eq hω hX₁ hX₂ hR₁ hR₂ hn hδ h, abs_div, abs_mul, hb]
  have hV : |(V₁ * conj V₂).im| ≤ ρ₁ / n * (ρ₂ / n) :=
    calc |(V₁ * conj V₂).im| ≤ ‖V₁ * conj V₂‖ := Complex.abs_im_le_norm _
      _ = ‖V₁‖ * ‖V₂‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ρ₁ / n * (ρ₂ / n) := mul_le_mul h₁ h₂ (norm_nonneg _) hr₁
  calc n * |ω * w.M| * |(V₁ * conj V₂).im| / |determinant w ω n|
      ≤ n * |ω * w.M| * (ρ₁ / n * (ρ₂ / n)) / |determinant w ω n| := by gcongr
    _ = |ω * w.M| * ρ₁ * ρ₂ / (n * |determinant w ω n|) := by field_simp

/-- The harmonic power as a fraction of the fundamental limit `ρ₁ρ₂/|ωM|`: if
`n⁴M² < (n² − 1)²L₁L₂` (that is, `δ > 0`) and `‖V_k‖ ≤ ρ_k/n`, then
`|Re(V₁ Ī₁)| ≤ nM²/((n² − 1)²L₁L₂ − n⁴M²) · ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem abs_power_le_fundamental {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hD : (n : ℝ) ^ 4 * w.M ^ 2 < ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L))
    (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁ / n)
    (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    |(V₁ * conj I₁).re| ≤ n * w.M ^ 2 /
        (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2) *
      (ρ₁ * ρ₂ / |ω * w.M|) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hδ : 0 < determinant w ω n := (determinant_pos_iff hω hn).mpr hD
  have hle := abs_power_le hω hX₁ hX₂ hR₁ hR₂ hn hδ.ne' h h₁ h₂
  rw [abs_of_pos hδ, determinant_eq hn] at hle
  refine hle.trans_eq ?_
  have hDpos : 0 < ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2 :=
    sub_pos.mpr hD
  rcases eq_or_ne w.M 0 with hM | hM
  · simp [hM]
  · have hωa : 0 < |ω| := abs_pos.mpr hω
    have hMa : 0 < |w.M| := abs_pos.mpr hM
    rw [abs_mul, ← sq_abs w.M, ← sq_abs ω]
    field_simp

/-- The primary harmonic current: with `‖V_k‖ ≤ ρ_k/n` and `δ ≠ 0`,
`‖I₁‖ ≤ (|c|ρ₁ + |b|ρ₂)/(n|δ|)`. -/
@[tmio M, powerlib_domain] theorem norm_current₁_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ} (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁ / n) (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    ‖I₁‖ ≤ (|harmonicReactance w.secondary.L ω n| * ρ₁ + |n * ω * w.M| * ρ₂) /
      (n * |determinant w ω n|) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hδa : 0 < |determinant w ω n| := abs_pos.mpr hδ
  rw [(currents_eq hω hX₁ hX₂ hR₁ hR₂ hn hδ h).1, norm_div, norm_neg, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(harmonicReactance w.secondary.L ω n : ℂ) * V₁ - ((n * ω * w.M : ℝ) : ℂ) * V₂‖ /
        |determinant w ω n|
      ≤ (|harmonicReactance w.secondary.L ω n| * (ρ₁ / n) + |n * ω * w.M| * (ρ₂ / n)) /
          |determinant w ω n| := by
        gcongr
        calc ‖(harmonicReactance w.secondary.L ω n : ℂ) * V₁ - ((n * ω * w.M : ℝ) : ℂ) * V₂‖
            ≤ ‖(harmonicReactance w.secondary.L ω n : ℂ) * V₁‖ +
                ‖((n * ω * w.M : ℝ) : ℂ) * V₂‖ := norm_sub_le _ _
          _ = |harmonicReactance w.secondary.L ω n| * ‖V₁‖ + |n * ω * w.M| * ‖V₂‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
          _ ≤ _ := by gcongr
    _ = _ := by field_simp

/-- The secondary harmonic current: with `‖V_k‖ ≤ ρ_k/n` and `δ ≠ 0`,
`‖I₂‖ ≤ (|b|ρ₁ + |a|ρ₂)/(n|δ|)`. -/
@[tmio M, powerlib_domain] theorem norm_current₂_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ} (hω : ω ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hn : n ≠ 0)
    (hδ : determinant w ω n ≠ 0) (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁ / n) (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    ‖I₂‖ ≤ (|n * ω * w.M| * ρ₁ + |harmonicReactance w.primary.L ω n| * ρ₂) /
      (n * |determinant w ω n|) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hδa : 0 < |determinant w ω n| := abs_pos.mpr hδ
  rw [(currents_eq hω hX₁ hX₂ hR₁ hR₂ hn hδ h).2, norm_div, norm_neg, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(harmonicReactance w.primary.L ω n : ℂ) * V₂ - ((n * ω * w.M : ℝ) : ℂ) * V₁‖ /
        |determinant w ω n|
      ≤ (|n * ω * w.M| * (ρ₁ / n) + |harmonicReactance w.primary.L ω n| * (ρ₂ / n)) /
          |determinant w ω n| := by
        gcongr
        calc ‖(harmonicReactance w.primary.L ω n : ℂ) * V₂ - ((n * ω * w.M : ℝ) : ℂ) * V₁‖
            ≤ ‖(harmonicReactance w.primary.L ω n : ℂ) * V₂‖ +
                ‖((n * ω * w.M : ℝ) : ℂ) * V₁‖ := norm_sub_le _ _
          _ = |harmonicReactance w.primary.L ω n| * ‖V₂‖ + |n * ω * w.M| * ‖V₁‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
          _ ≤ |harmonicReactance w.primary.L ω n| * (ρ₂ / n) + |n * ω * w.M| * (ρ₁ / n) := by
              gcongr
          _ = |n * ω * w.M| * (ρ₁ / n) + |harmonicReactance w.primary.L ω n| * (ρ₂ / n) := by
              ring
    _ = _ := by field_simp

end powerlib.WPT.Harmonics
