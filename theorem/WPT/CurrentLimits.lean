import theorem.WPT.Compensation

/-! # Current limits of the resonant link with two active bridges

How large the coil currents of an inductive power link can be made when both coils are driven by
bridges whose fundamental voltages are bounded. Whatever the modulation (phase shift, duty,
frequency), in the fundamental-harmonic picture each bridge contributes one phasor of bounded
magnitude `‖V_k‖ ≤ ρ_k`, and the coil currents are the response of the coupled pair to the two
phasors. Four limits follow, each exact or attained.

* Power balance (every frequency and every tuning): the currents lie in the ellipse
  `R₁ ‖I₁‖² + R₂ ‖I₂‖² ≤ ρ₁ ‖I₁‖ + ρ₂ ‖I₂‖`; the winding losses bound the currents.
* Resonant link (both coils tuned): the largest primary current is exactly
  `(R₂ ρ₁ + |ωM| ρ₂)/(R₁R₂ + (ωM)²)`, the largest secondary current exactly
  `(|ωM| ρ₁ + R₁ ρ₂)/(R₁R₂ + (ωM)²)`; both are attained by bridge phasors of full magnitude with
  the right relative phase.
* Lossless resonant link: the link is a gyrator, `I₁ = −j V₂/(ωM)`, `I₂ = −j V₁/(ωM)`: the primary
  current is set by the secondary bridge and the secondary current by the primary bridge. The
  reachable current pairs are exactly the bidisk `‖I₁‖ ≤ ρ₂/|ωM|`, `‖I₂‖ ≤ ρ₁/|ωM|`, and the
  transferred power is at most `ρ₁ ρ₂/|ωM|`, attained.
* Component stress: the series capacitor of coil `k` carries the voltage `S_k ‖I_k‖/|ω|`, so a
  capacitor rating `V_C,max` caps the current at `|ω| V_C,max/S_k`; with the rating the reachable
  set of the lossless resonant link is the bidisk with both radii reduced to the smaller cap.

For a full bridge on the DC voltage `V_dc`, the fundamental of every switching pattern has peak
amplitude at most `4V_dc/π` (RMS `2√2 V_dc/π`), attained by the square wave
(`theorem/SpecialFunctions/Fundamental.lean`); that is the radius `ρ_k` of the bridge.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`) at one angular
  frequency `ω ≠ 0`, RMS phasors in sinusoidal steady state: both ports driven by the fundamental
  voltage phasors `V₁`, `V₂` of the two bridges, port currents `I₁`, `I₂` into the dotted
  terminals (`Driven`, the two-port equations `Grid.TwoPort.Equations` of the impedance matrix at
  `jω`). A passive rectifier is the special case of `V₂` in phase with `−I₂`.
* Fundamental-harmonic approximation: the harmonics of the bridge voltages and their currents are
  not part of this model (for a high-quality-factor tank they are small; their exact contribution
  needs the time-domain model). The bridge constraint is the bound `‖V_k‖ ≤ ρ_k` on the
  fundamental; dead time, zero-voltage-switching conditions, device current and thermal ratings,
  core saturation and the DC-link dynamics are not modelled, except the capacitor voltage rating.
* The exact suprema use the resonant tuning `X₁(ω) = X₂(ω) = 0` and nonnegative winding
  resistances; the gyrator statements use lossless windings and `ωM ≠ 0`.

Source: the fundamental-harmonic analysis of resonant converters and of bidirectional
series–series inductive power transfer driven by two active bridges (Steigerwald, *IEEE Trans.
Power Electron.* 3 (1988) 174–182, for the fundamental-harmonic analysis of resonant converters);
the impedance matrix of `theorem/Passive/Coupled.lean` and the two-port equations of
`theorem/Grid/TwoPort.lean`.

Results.
* `Driven`, `driven_iff` (the two phasor equations written out), `power_balance`
  (`Re(V₁ Ī₁) + Re(V₂ Ī₂) = R₁|I₁|² + R₂|I₂|²`, every frequency and tuning), `loss_le`
  (the ellipse `R₁‖I₁‖² + R₂‖I₂‖² ≤ ρ₁‖I₁‖ + ρ₂‖I₂‖`).
* Resonant link: `determinant` (`R₁R₂ + (ωM)²`), `currents_eq` (`I₁ = (R₂V₁ − jωM V₂)/Δ`,
  `I₂ = (R₁V₂ − jωM V₁)/Δ`), `driven_currents` (these solve the equations),
  `norm_current₁_le`, `exists_current₁_eq` (the exact supremum of `‖I₁‖` and its attainment),
  `norm_current₂_le`, `exists_current₂_eq` (the same for `‖I₂‖`).
* Lossless resonant link: `currents_lossless` (the gyrator law), `reachable_iff` (the reachable
  current pairs are exactly the bidisk), `power_le`, `exists_power_eq` (the transferred power
  `Re(V₁ Ī₁) ≤ ρ₁ρ₂/|ωM|`, attained).
* Stress: `norm_capacitorVoltage` (`‖V_C‖ = S‖I‖/|ω|`), `capacitorRating_iff`
  (`‖V_C‖ ≤ V_C,max ↔ ‖I‖ ≤ |ω| V_C,max/S`), `reachable_rated_iff` (lossless resonant link with
  capacitor ratings: the bidisk with the smaller radii).
-/

noncomputable section

namespace powerlib.WPT.CurrentLimits

open Complex ComplexConjugate

variable (w : Passive.Coupled) (ω : ℝ)

/-- Both ports driven: `V₁ = Z₁(jω) I₁ + jωM I₂`, `V₂ = jωM I₁ + Z₂(jω) I₂`. -/
def Driven (V₁ V₂ I₁ I₂ : ℂ) : Prop :=
  Grid.TwoPort.Equations (w.impedanceMatrix (ω * I)) V₁ V₂ I₁ I₂

/-- The two phasor equations written out, with `Z_k(jω) = R_k + j X_k(ω)`. -/
@[tmio M, powerlib_domain] theorem driven_iff (V₁ V₂ I₁ I₂ : ℂ) :
    Driven w ω V₁ V₂ I₁ I₂ ↔
      V₁ = (w.primary.R + w.primary.reactance ω * I) * I₁ + ((ω * w.M : ℝ) : ℂ) * I * I₂ ∧
        V₂ = ((ω * w.M : ℝ) : ℂ) * I * I₁ +
          (w.secondary.R + w.secondary.reactance ω * I) * I₂ := by
  simp only [Driven, Grid.TwoPort.Equations, Passive.Coupled.impedanceMatrix, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Passive.SeriesRLC.impedance_jω]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linear_combination h1, by linear_combination h2⟩

/-- Power balance at every frequency and tuning: the real power the two bridges deliver is the
winding loss, `Re(V₁ Ī₁) + Re(V₂ Ī₂) = R₁|I₁|² + R₂|I₂|²`. -/
@[tmio M, powerlib_domain] theorem power_balance {V₁ V₂ I₁ I₂ : ℂ} (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re + (V₂ * conj I₂).re =
      w.primary.R * normSq I₁ + w.secondary.R * normSq I₂ := by
  obtain ⟨h1, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [h1, h2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- The loss ellipse: with bridge phasors `‖V_k‖ ≤ ρ_k`, at every frequency and tuning,
`R₁‖I₁‖² + R₂‖I₂‖² ≤ ρ₁‖I₁‖ + ρ₂‖I₂‖`. -/
@[tmio M, powerlib_domain] theorem loss_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    w.primary.R * ‖I₁‖ ^ 2 + w.secondary.R * ‖I₂‖ ^ 2 ≤ ρ₁ * ‖I₁‖ + ρ₂ * ‖I₂‖ := by
  have hb := power_balance w ω h
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hb
  have e1 : (V₁ * conj I₁).re ≤ ρ₁ * ‖I₁‖ := by
    calc (V₁ * conj I₁).re ≤ ‖V₁ * conj I₁‖ := Complex.re_le_norm _
      _ = ‖V₁‖ * ‖I₁‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ρ₁ * ‖I₁‖ := mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
  have e2 : (V₂ * conj I₂).re ≤ ρ₂ * ‖I₂‖ := by
    calc (V₂ * conj I₂).re ≤ ‖V₂ * conj I₂‖ := Complex.re_le_norm _
      _ = ‖V₂‖ * ‖I₂‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ρ₂ * ‖I₂‖ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
  linarith

/-! ## The resonant link -/

/-- The determinant `Δ = R₁R₂ + (ωM)²` of the resonant link. -/
def determinant : ℝ := w.primary.R * w.secondary.R + (ω * w.M) ^ 2

/-- The resonant link: `I₁ = (R₂ V₁ − jωM V₂)/Δ`, `I₂ = (R₁ V₂ − jωM V₁)/Δ`. -/
@[tmio M, powerlib_domain] theorem currents_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    I₁ = (w.secondary.R * V₁ - ((ω * w.M : ℝ) : ℂ) * I * V₂) / (determinant w ω : ℂ) ∧
      I₂ = (w.primary.R * V₂ - ((ω * w.M : ℝ) : ℂ) * I * V₁) / (determinant w ω : ℂ) := by
  obtain ⟨h1, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [hX₁] at h1
  rw [hX₂] at h2
  have hΔ' : (determinant w ω : ℂ) ≠ 0 := by exact_mod_cast hΔ
  simp only [determinant] at hΔ' ⊢
  push_cast at hΔ' h1 h2 ⊢
  constructor
  · rw [eq_div_iff hΔ']
    linear_combination (-(w.secondary.R : ℂ)) * h1 + ((ω : ℂ) * w.M * I) * h2 +
      ((ω : ℂ) ^ 2 * w.M ^ 2 * I₁) * I_sq
  · rw [eq_div_iff hΔ']
    linear_combination ((ω : ℂ) * w.M * I) * h1 + (-(w.primary.R : ℂ)) * h2 +
      ((ω : ℂ) ^ 2 * w.M ^ 2 * I₂) * I_sq

/-- The currents `(R₂ V₁ − jωM V₂)/Δ`, `(R₁ V₂ − jωM V₁)/Δ` solve the resonant link. -/
@[tmio M, powerlib_domain] theorem driven_currents (V₁ V₂ : ℂ)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) :
    Driven w ω V₁ V₂
      ((w.secondary.R * V₁ - ((ω * w.M : ℝ) : ℂ) * I * V₂) / (determinant w ω : ℂ))
      ((w.primary.R * V₂ - ((ω * w.M : ℝ) : ℂ) * I * V₁) / (determinant w ω : ℂ)) := by
  rw [driven_iff, hX₁, hX₂]
  have hΔ' : (determinant w ω : ℂ) ≠ 0 := by exact_mod_cast hΔ
  have hD : (determinant w ω : ℂ) =
      (w.primary.R : ℂ) * w.secondary.R + ((ω * w.M : ℝ) : ℂ) ^ 2 := by
    simp [determinant]
  constructor
  · rw [Complex.ofReal_zero, zero_mul, add_zero, mul_div_assoc', mul_div_assoc',
      ← add_div, eq_div_iff hΔ', hD]
    linear_combination (((ω * w.M : ℝ) : ℂ) ^ 2 * V₁) * I_sq
  · rw [Complex.ofReal_zero, zero_mul, add_zero, mul_div_assoc', mul_div_assoc',
      ← add_div, eq_div_iff hΔ', hD]
    linear_combination (((ω * w.M : ℝ) : ℂ) ^ 2 * V₂) * I_sq

/-- The primary current of the resonant link never exceeds `(R₂ρ₁ + |ωM|ρ₂)/Δ`. -/
@[tmio M, powerlib_domain] theorem norm_current₁_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₂ : 0 ≤ w.secondary.R) (hΔ : 0 < determinant w ω) (h : Driven w ω V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    ‖I₁‖ ≤ (w.secondary.R * ρ₁ + |ω * w.M| * ρ₂) / determinant w ω := by
  rw [(currents_eq w ω hX₁ hX₂ hΔ.ne' h).1, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hΔ]
  apply div_le_div_of_nonneg_right _ hΔ.le
  calc ‖(w.secondary.R : ℂ) * V₁ - ((ω * w.M : ℝ) : ℂ) * I * V₂‖
      ≤ ‖(w.secondary.R : ℂ) * V₁‖ + ‖((ω * w.M : ℝ) : ℂ) * I * V₂‖ := norm_sub_le _ _
    _ = w.secondary.R * ‖V₁‖ + |ω * w.M| * ‖V₂‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hR₂, mul_one]
    _ ≤ w.secondary.R * ρ₁ + |ω * w.M| * ρ₂ := by gcongr

/-- The supremum of the primary current is attained: with `ωM ≠ 0` the bridge phasors
`V₁ = ρ₁`, `V₂ = j ρ₂ sgn(ωM)` give `‖I₁‖ = (R₂ρ₁ + |ωM|ρ₂)/Δ`. -/
@[tmio M, powerlib_domain] theorem exists_current₁_eq {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₂ : 0 ≤ w.secondary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      ‖I₁‖ = (w.secondary.R * ρ₁ + |ω * w.M| * ρ₂) / determinant w ω := by
  set m := ω * w.M with hmdef
  have hma : 0 < |m| := abs_pos.mpr hm
  refine ⟨ρ₁, I * ((ρ₂ * (m / |m|) : ℝ) : ℂ), _, _, ?_, ?_,
    driven_currents w ω _ _ hX₁ hX₂ hΔ.ne', ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₁]
  · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hρ₂, abs_div, abs_abs, div_self hma.ne', mul_one]
  · have hsq : m * (m / |m|) = |m| := by
      rw [← mul_div_assoc, ← sq, ← sq_abs, sq, mul_div_assoc, div_self hma.ne', mul_one]
    have hr : m * (ρ₂ * (m / |m|)) = ρ₂ * |m| := by
      calc m * (ρ₂ * (m / |m|)) = ρ₂ * (m * (m / |m|)) := by ring
        _ = ρ₂ * |m| := by rw [hsq]
    have e2 : ((m : ℝ) : ℂ) * I * (I * ((ρ₂ * (m / |m|) : ℝ) : ℂ)) = -((ρ₂ * |m| : ℝ) : ℂ) := by
      calc ((m : ℝ) : ℂ) * I * (I * ((ρ₂ * (m / |m|) : ℝ) : ℂ))
          = ((m * (ρ₂ * (m / |m|)) : ℝ) : ℂ) * (I * I) := by push_cast; ring
        _ = -((ρ₂ * |m| : ℝ) : ℂ) := by rw [hr, I_mul_I]; ring
    have e : (w.secondary.R : ℂ) * (ρ₁ : ℂ) - ((m : ℝ) : ℂ) * I *
        (I * ((ρ₂ * (m / |m|) : ℝ) : ℂ)) = ((w.secondary.R * ρ₁ + |m| * ρ₂ : ℝ) : ℂ) := by
      rw [e2]
      push_cast
      ring
    rw [e, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hΔ, abs_of_nonneg (by positivity)]

/-- The secondary current of the resonant link never exceeds `(|ωM|ρ₁ + R₁ρ₂)/Δ`. -/
@[tmio M, powerlib_domain] theorem norm_current₂_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 ≤ w.primary.R) (hΔ : 0 < determinant w ω) (h : Driven w ω V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    ‖I₂‖ ≤ (|ω * w.M| * ρ₁ + w.primary.R * ρ₂) / determinant w ω := by
  rw [(currents_eq w ω hX₁ hX₂ hΔ.ne' h).2, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hΔ]
  apply div_le_div_of_nonneg_right _ hΔ.le
  calc ‖(w.primary.R : ℂ) * V₂ - ((ω * w.M : ℝ) : ℂ) * I * V₁‖
      ≤ ‖(w.primary.R : ℂ) * V₂‖ + ‖((ω * w.M : ℝ) : ℂ) * I * V₁‖ := norm_sub_le _ _
    _ = w.primary.R * ‖V₂‖ + |ω * w.M| * ‖V₁‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hR₁, mul_one]
    _ ≤ |ω * w.M| * ρ₁ + w.primary.R * ρ₂ := by nlinarith [abs_nonneg (ω * w.M), norm_nonneg V₁]

/-- `m · (ρ (m/|m|)) = ρ |m|`, and the bridge phasor `j ρ sgn(m)` turns `−j m` into `ρ|m|`. -/
@[tmio T, powerlib_foundation] private theorem gyrate_sign {m ρ : ℝ} (hm : m ≠ 0) :
    ((m : ℝ) : ℂ) * I * (I * ((ρ * (m / |m|) : ℝ) : ℂ)) = -((ρ * |m| : ℝ) : ℂ) := by
  have hma : 0 < |m| := abs_pos.mpr hm
  have hsq : m * (m / |m|) = |m| := by
    rw [← mul_div_assoc, ← sq, ← sq_abs, sq, mul_div_assoc, div_self hma.ne', mul_one]
  have hr : m * (ρ * (m / |m|)) = ρ * |m| := by
    calc m * (ρ * (m / |m|)) = ρ * (m * (m / |m|)) := by ring
      _ = ρ * |m| := by rw [hsq]
  calc ((m : ℝ) : ℂ) * I * (I * ((ρ * (m / |m|) : ℝ) : ℂ))
      = ((m * (ρ * (m / |m|)) : ℝ) : ℂ) * (I * I) := by push_cast; ring
    _ = -((ρ * |m| : ℝ) : ℂ) := by rw [hr, I_mul_I]; ring

/-- `c j (−j V/c) = V` for `c ≠ 0`. -/
@[tmio T, powerlib_foundation] private theorem gyrate_inv {c : ℂ} (hc : c ≠ 0) (V : ℂ) :
    c * I * (-(I * V) / c) = V := by
  rw [mul_div_assoc', div_eq_iff hc]
  linear_combination (-c * V) * I_sq

@[tmio T, powerlib_foundation] private theorem norm_signPhasor {m ρ : ℝ} (hm : m ≠ 0)
    (hρ : 0 ≤ ρ) : ‖I * ((ρ * (m / |m|) : ℝ) : ℂ)‖ = ρ := by
  have hma : 0 < |m| := abs_pos.mpr hm
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hρ, abs_div, abs_abs, div_self hma.ne', mul_one]

/-- The supremum of the secondary current is attained: with `ωM ≠ 0` the bridge phasors
`V₁ = j ρ₁ sgn(ωM)`, `V₂ = ρ₂` give `‖I₂‖ = (|ωM|ρ₁ + R₁ρ₂)/Δ`. -/
@[tmio M, powerlib_domain] theorem exists_current₂_eq {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 ≤ w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      ‖I₂‖ = (|ω * w.M| * ρ₁ + w.primary.R * ρ₂) / determinant w ω := by
  refine ⟨I * ((ρ₁ * ((ω * w.M) / |ω * w.M|) : ℝ) : ℂ), ρ₂, _, _,
    (norm_signPhasor hm hρ₁).le, ?_, driven_currents w ω _ _ hX₁ hX₂ hΔ.ne', ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₂]
  · have e : (w.primary.R : ℂ) * (ρ₂ : ℂ) - ((ω * w.M : ℝ) : ℂ) * I *
        (I * ((ρ₁ * ((ω * w.M) / |ω * w.M|) : ℝ) : ℂ)) =
        ((|ω * w.M| * ρ₁ + w.primary.R * ρ₂ : ℝ) : ℂ) := by
      rw [gyrate_sign hm]
      push_cast
      ring
    rw [e, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hΔ, abs_of_nonneg (by positivity)]

/-! ## The lossless resonant link: a gyrator -/

/-- The lossless resonant link is a gyrator: `I₁ = −j V₂/(ωM)`, `I₂ = −j V₁/(ωM)`. The primary
current is set by the secondary bridge and the secondary current by the primary bridge. -/
@[tmio M, powerlib_domain] theorem currents_lossless {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    I₁ = -(I * V₂) / ((ω * w.M : ℝ) : ℂ) ∧ I₂ = -(I * V₁) / ((ω * w.M : ℝ) : ℂ) := by
  have hΔ : determinant w ω ≠ 0 := by
    simp only [determinant, hR₁, hR₂, zero_mul, zero_add]
    exact pow_ne_zero 2 hm
  have hm' : ((ω * w.M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
  obtain ⟨h1, h2⟩ := currents_eq w ω hX₁ hX₂ hΔ h
  simp only [determinant, hR₁, hR₂, Complex.ofReal_zero, zero_mul, zero_add, zero_sub] at h1 h2
  constructor
  · rw [h1]
    push_cast at hm' ⊢
    field_simp
  · rw [h2]
    push_cast at hm' ⊢
    field_simp

/-- The reachable currents of the lossless resonant link are exactly the bidisk
`‖I₁‖ ≤ ρ₂/|ωM|`, `‖I₂‖ ≤ ρ₁/|ωM|`: some bridge phasors with `‖V_k‖ ≤ ρ_k` drive the currents
`(I₁, I₂)` iff they lie in it. -/
@[tmio M, powerlib_domain] theorem reachable_iff {ρ₁ ρ₂ : ℝ} (I₁ I₂ : ℂ)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0) :
    (∃ V₁ V₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂) ↔
      ‖I₁‖ ≤ ρ₂ / |ω * w.M| ∧ ‖I₂‖ ≤ ρ₁ / |ω * w.M| := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hnorm : ∀ V : ℂ, ‖-(I * V) / ((ω * w.M : ℝ) : ℂ)‖ = ‖V‖ / |ω * w.M| := fun V => by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  constructor
  · rintro ⟨V₁, V₂, h₁, h₂, h⟩
    obtain ⟨e1, e2⟩ := currents_lossless w ω hX₁ hX₂ hR₁ hR₂ hm h
    rw [e1, e2, hnorm, hnorm]
    exact ⟨div_le_div_of_nonneg_right h₂ hma.le, div_le_div_of_nonneg_right h₁ hma.le⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨((ω * w.M : ℝ) : ℂ) * I * I₂, ((ω * w.M : ℝ) : ℂ) * I * I₁, ?_, ?_, ?_⟩
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [le_div_iff₀ hma] at h₂
      linarith
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [le_div_iff₀ hma] at h₁
      linarith
    · rw [driven_iff, hX₁, hX₂, hR₁, hR₂]
      push_cast
      constructor <;> ring

/-- The lossless resonant link transfers at most the power `ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem power_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    (V₁ * conj I₁).re ≤ ρ₁ * ρ₂ / |ω * w.M| := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hI₁ : ‖I₁‖ = ‖V₂‖ / |ω * w.M| := by
    rw [(currents_lossless w ω hX₁ hX₂ hR₁ hR₂ hm h).1, norm_div, norm_neg, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc (V₁ * conj I₁).re ≤ ‖V₁ * conj I₁‖ := Complex.re_le_norm _
    _ = ‖V₁‖ * (‖V₂‖ / |ω * w.M|) := by rw [norm_mul, Complex.norm_conj, hI₁]
    _ ≤ ρ₁ * (ρ₂ / |ω * w.M|) := by
      gcongr
      exact (norm_nonneg V₁).trans h₁
    _ = ρ₁ * ρ₂ / |ω * w.M| := by ring

/-- The power limit is attained: `V₁ = ρ₁`, `V₂ = j ρ₂ sgn(ωM)` transfer `ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem exists_power_eq {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      (V₁ * conj I₁).re = ρ₁ * ρ₂ / |ω * w.M| := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hm' : ((ω * w.M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
  set V₂ : ℂ := I * ((ρ₂ * ((ω * w.M) / |ω * w.M|) : ℝ) : ℂ)
  have hI₁ : -(I * V₂) / ((ω * w.M : ℝ) : ℂ) = ((ρ₂ / |ω * w.M| : ℝ) : ℂ) := by
    rw [div_eq_iff hm']
    have := gyrate_sign (ρ := ρ₂) hm
    have hmr : (ρ₂ / |ω * w.M|) * (ω * w.M) = ρ₂ * ((ω * w.M) / |ω * w.M|) := by ring
    have hc : ((ρ₂ / |ω * w.M| : ℝ) : ℂ) * ((ω * w.M : ℝ) : ℂ) =
        ((ρ₂ * ((ω * w.M) / |ω * w.M|) : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, hmr]
    rw [hc]
    simp only [V₂]
    linear_combination (-((ρ₂ * ((ω * w.M) / |ω * w.M|) : ℝ) : ℂ)) * I_sq
  refine ⟨ρ₁, V₂, -(I * V₂) / ((ω * w.M : ℝ) : ℂ), -(I * (ρ₁ : ℂ)) / ((ω * w.M : ℝ) : ℂ), ?_,
    (norm_signPhasor hm hρ₂).le, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₁]
  · rw [driven_iff, hX₁, hX₂, hR₁, hR₂]
    simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero]
    exact ⟨(gyrate_inv hm' _).symm, (gyrate_inv hm' _).symm⟩
  · rw [hI₁, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring

/-! ## Component stress -/

/-- The voltage phasor `(S/(jω)) I` across the series capacitor of a coil carrying `I`. -/
def capacitorVoltage (b : Passive.SeriesRLC) (ω : ℝ) (I' : ℂ) : ℂ := b.S / (ω * I) * I'

/-- The capacitor voltage magnitude `S‖I‖/|ω|` (`S ≥ 0`). -/
@[tmio M, powerlib_domain] theorem norm_capacitorVoltage {b : Passive.SeriesRLC} (hS : 0 ≤ b.S)
    (ω : ℝ) (I' : ℂ) : ‖capacitorVoltage b ω I'‖ = b.S * ‖I'‖ / |ω| := by
  rw [capacitorVoltage, norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS]
  ring

/-- A capacitor voltage rating caps the coil current: `‖V_C‖ ≤ V_C,max ↔ ‖I‖ ≤ |ω| V_C,max/S`. -/
@[tmio M, powerlib_domain] theorem capacitorRating_iff {b : Passive.SeriesRLC} (hS : 0 < b.S)
    {ω : ℝ} (hω : ω ≠ 0) (I' : ℂ) (Vmax : ℝ) :
    ‖capacitorVoltage b ω I'‖ ≤ Vmax ↔ ‖I'‖ ≤ |ω| * Vmax / b.S := by
  have hωa : 0 < |ω| := abs_pos.mpr hω
  rw [norm_capacitorVoltage hS.le, div_le_iff₀ hωa, le_div_iff₀ hS]
  constructor <;> intro h <;> linarith

/-- With capacitor ratings the reachable currents of the lossless resonant link are exactly the
bidisk with the smaller radii: `‖I₁‖ ≤ min(ρ₂/|ωM|, |ω| V_C1/S₁)`,
`‖I₂‖ ≤ min(ρ₁/|ωM|, |ω| V_C2/S₂)`. -/
@[tmio M, powerlib_domain] theorem reachable_rated_iff {ρ₁ ρ₂ Vc₁ Vc₂ : ℝ} (I₁ I₂ : ℂ)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (hS₁ : 0 < w.primary.S) (hS₂ : 0 < w.secondary.S) :
    (∃ V₁ V₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        ‖capacitorVoltage w.primary ω I₁‖ ≤ Vc₁ ∧ ‖capacitorVoltage w.secondary ω I₂‖ ≤ Vc₂) ↔
      ‖I₁‖ ≤ min (ρ₂ / |ω * w.M|) (|ω| * Vc₁ / w.primary.S) ∧
        ‖I₂‖ ≤ min (ρ₁ / |ω * w.M|) (|ω| * Vc₂ / w.secondary.S) := by
  have hω : ω ≠ 0 := left_ne_zero_of_mul hm
  rw [le_min_iff, le_min_iff, ← capacitorRating_iff hS₁ hω, ← capacitorRating_iff hS₂ hω]
  constructor
  · rintro ⟨V₁, V₂, h₁, h₂, h, hc₁, hc₂⟩
    obtain ⟨r₁, r₂⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
    exact ⟨⟨r₁, hc₁⟩, ⟨r₂, hc₂⟩⟩
  · rintro ⟨⟨r₁, hc₁⟩, ⟨r₂, hc₂⟩⟩
    obtain ⟨V₁, V₂, h₁, h₂, h⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mpr ⟨r₁, r₂⟩
    exact ⟨V₁, V₂, h₁, h₂, h, hc₁, hc₂⟩

end powerlib.WPT.CurrentLimits
