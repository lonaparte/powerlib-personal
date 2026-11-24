import theorem.WPT.LossyLimits

/-! # Flux-limited output power of the lossy link with two active bridges

The largest real power the secondary bridge of a lossy series–series link can absorb when the
fundamental flux linkage of one coil is bounded, alone and together with the bridge limits
`‖V_k‖ ≤ ρ_k` of `theorem/WPT/LossyLimits.lean`. The output power is `−Re(V₂ Ī₂)`; the flux
linkages are `ψ₁ = L₁I₁ + MI₂`, `ψ₂ = MI₁ + L₂I₂` (`Passive.Coupled.flux₁`, `flux₂`).

* Secondary flux. Since `V₂ = jωM I₁ + Z₂I₂ = jω(ψ₂ − L₂I₂) + Z₂I₂` and the self-inductive and
  capacitive voltages carry no real power, at every tuning and for any primary
  `−Re(V₂ Ī₂) = ω Im(ψ₂ Ī₂) − R₂‖I₂‖²`: the secondary bridge receives what the induced voltage
  `jωψ₂` delivers less the secondary winding loss. Under `‖ψ₂‖² ≤ Ψ₂²` this is at most
  `|ω|Ψ₂‖I₂‖ − R₂‖I₂‖² ≤ ω²Ψ₂²/(4R₂)`, the matched-load power of a source `|ω|Ψ₂` behind `R₂`,
  attained (`R₂ > 0`, `M ≠ 0`) at `ψ₂ = Ψ₂`, `I₂ = −j ωΨ₂/(2R₂)`. The limit depends only on `ω`,
  `Ψ₂` and `R₂`: not on `M`, `L₂`, the primary or the tuning.
* Primary flux. With `L₁ ≠ 0`, `I₁ = (ψ₁ − MI₂)/L₁`, so at every tuning
  `−Re(V₂ Ī₂) = (ωM/L₁) Im(ψ₁ Ī₂) − R₂‖I₂‖²`: the primary flux induces in the secondary the
  voltage `jω(M/L₁)ψ₁`. Under `‖ψ₁‖² ≤ Ψ₁²` the output is at most `(ωM)²Ψ₁²/(4L₁²R₂)`, attained
  (`R₂ > 0`) at `ψ₁ = Ψ₁`, `I₂ = −j ωMΨ₁/(2L₁R₂)`.
* Bridges and one flux bound (resonant link, `R₁ > 0`): every admissible operating point delivers
  at most the smaller of `LossyLimits.outputLimit` and the flux limit. The bridge limit is exact
  when the flux at the bridge optimum `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)` meets the bound; there the
  currents are `I₁ = (R₂ρ₁ + |ωM|v⋆)/Δ` (real) and `I₂ = ±j(|ωM|ρ₁ − R₁v⋆)/Δ` (imaginary), so
  `‖ψ₁‖² = (L₁²(R₂ρ₁ + |ωM|v⋆)² + M²(|ωM|ρ₁ − R₁v⋆)²)/Δ²` and
  `‖ψ₂‖² = (M²(R₂ρ₁ + |ωM|v⋆)² + L₂²(|ωM|ρ₁ − R₁v⋆)²)/Δ²`. The flux limit is exact when the
  bridge voltages of the flux optimizer above fit the bridges; on the resonant link they are, for
  the secondary flux,
  `‖V₁‖ = |Ψ₂|√((2R₁R₂ + (ωM)²)² + (ωR₁L₂)²)/(2R₂|M|)` and
  `‖V₂‖ = |ωΨ₂|√(R₂² + (ωL₂)²)/(2R₂)`, for the primary flux
  `‖V₁‖ = |Ψ₁|√((L₁(2R₁R₂ + (ωM)²))² + (ωR₁M²)²)/(2L₁²R₂)` and
  `‖V₂‖ = |ωMΨ₁|√((ωM²)² + (L₁R₂)²)/(2L₁²R₂)`; the theorems state these conditions squared.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`: linear
  magnetics, no saturation, hysteresis or core loss) at one angular frequency, RMS phasors in
  sinusoidal steady state: both ports driven by the fundamental voltage phasors `V₁`, `V₂`, port
  currents `I₁`, `I₂` into the dotted terminals (`CurrentLimits.Driven`); the boundary of
  `theorem/WPT/CurrentLimits.lean`.
* Fundamental-harmonic approximation: the flux bound `‖ψ_k‖² ≤ Ψ_k²` bounds the fundamental
  flux-linkage phasor of the linear model; how a core-saturation, core-loss or field-exposure
  rating translates into `Ψ_k` is not modelled, nor are harmonic fluxes. The bridge constraint is
  the bound `‖V_k‖ ≤ ρ_k` on the fundamental; dead time, zero-voltage switching, device and
  capacitor ratings and the DC-link dynamics are not modelled; bridge losses are not modelled.
* The flux identities hold at every tuning (the primary one for `L₁ ≠ 0`); the flux limits hold
  at every tuning, for any primary resistance and any bridge voltages, with `R₂ > 0` (and
  `L₁ ≠ 0` for the primary flux), and are attained without bridge limits for `M ≠ 0` (secondary
  flux). The statements with bridges use the resonant tuning `X₁(ω) = X₂(ω) = 0` and
  `ρ₁, ρ₂ ≥ 0`: the smaller-limit bounds `R₁, R₂ > 0`; the exactness of `LossyLimits.outputLimit`
  `R₁ > 0`, `Δ > 0` and `ωM ≠ 0` as in `theorem/WPT/LossyLimits.lean`; the exactness of the flux
  limits `R₂ > 0` with `M ≠ 0` (secondary) or `L₁ ≠ 0` (primary). Not covered here: the exact
  limit when the bridge and the flux bounds bind at once (neither exactness condition holds), and
  both flux bounds together; both are located exactly by Lagrangian duality in
  `theorem/WPT/LossyEnvelope.lean`.

Source: the coil pair and its flux linkages `Passive.Coupled.flux₁`, `Passive.Coupled.flux₂` of
`theorem/Passive/Coupled.lean`; the driven two-port `CurrentLimits.Driven`,
`CurrentLimits.driven_iff`, `CurrentLimits.currents_eq` and `CurrentLimits.driven_currents` of
`theorem/WPT/CurrentLimits.lean`; the bridge limit `LossyLimits.outputLimit` with
`LossyLimits.outputPower_le`, `LossyLimits.outputPower_optimum` and `LossyLimits.outputLimit_eq`
of `theorem/WPT/LossyLimits.lean`; the maximum-power-transfer (matched-load) bound of a source
behind a resistance.

Results.
* `secondaryFluxLimit` (`ω²Ψ₂²/(4R₂)`), `primaryFluxLimit` (`(ωM)²Ψ₁²/(4L₁²R₂)`).
* `outputPower_eq_flux₂` (`−Re(V₂ Ī₂) = ω Im(ψ₂ Ī₂) − R₂‖I₂‖²`, every tuning),
  `outputPower_eq_flux₁` (`−Re(V₂ Ī₂) = (ωM/L₁) Im(ψ₁ Ī₂) − R₂‖I₂‖²`, every tuning, `L₁ ≠ 0`).
* `outputPower_le_secondaryFluxLimit`, `isGreatest_secondaryFluxLimit` (under `‖ψ₂‖² ≤ Ψ₂²`
  the output is at most `ω²Ψ₂²/(4R₂)`, the exact maximum); `outputPower_le_primaryFluxLimit`,
  `isGreatest_primaryFluxLimit` (under `‖ψ₁‖² ≤ Ψ₁²` at most `(ωM)²Ψ₁²/(4L₁²R₂)`, exact).
* Bridges and flux: `outputPower_le_min_secondaryFluxLimit`, `outputPower_le_min_primaryFluxLimit`
  (`−Re(V₂ Ī₂) ≤ min(outputLimit, flux limit)`); `normSq_flux₁_at_optimum`,
  `normSq_flux₂_at_optimum` (the flux at the bridge optimum in closed form);
  `isGreatest_outputLimit_flux₁`, `isGreatest_outputLimit_flux₂` (`outputLimit` is the exact
  maximum under the bridges and the flux bound when the flux at the bridge optimum meets it);
  `isGreatest_primaryFluxLimit_bridges`, `isGreatest_secondaryFluxLimit_bridges` (the flux limit
  is the exact maximum under the bridges and the flux bound when the bridge voltages of the flux
  optimizer fit the bridges).
-/

noncomputable section

namespace powerlib.WPT.LossyFlux

open Complex ComplexConjugate CurrentLimits LossyLimits

variable (w : Passive.Coupled) (ω : ℝ)

/-- The secondary-flux limit of the output power, `ω²Ψ₂²/(4R₂)`. -/
def secondaryFluxLimit (Ψ₂ : ℝ) : ℝ := ω ^ 2 * Ψ₂ ^ 2 / (4 * w.secondary.R)

/-- The primary-flux limit of the output power, `(ωM)²Ψ₁²/(4L₁²R₂)`. -/
def primaryFluxLimit (Ψ₁ : ℝ) : ℝ :=
  (ω * w.M) ^ 2 * Ψ₁ ^ 2 / (4 * w.primary.L ^ 2 * w.secondary.R)

/-! ## The output power through the flux linkages -/

/-- At every tuning: `−Re(V₂ Ī₂) = ωM Im(I₁ Ī₂) − R₂‖I₂‖²`. -/
@[tmio M, powerlib_domain] private theorem outputPower_eq_mutual {V₁ V₂ I₁ I₂ : ℂ}
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re = ω * w.M * (I₁ * conj I₂).im - w.secondary.R * normSq I₂ := by
  obtain ⟨-, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [h2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- At every tuning, with any primary, the output power passes through the secondary flux:
`−Re(V₂ Ī₂) = ω Im(ψ₂ Ī₂) − R₂‖I₂‖²`. -/
@[tmio M, powerlib_domain] theorem outputPower_eq_flux₂ {V₁ V₂ I₁ I₂ : ℂ}
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re = ω * (w.flux₂ I₁ I₂ * conj I₂).im - w.secondary.R * normSq I₂ := by
  rw [outputPower_eq_mutual w ω h]
  simp only [Passive.Coupled.flux₂, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- At every tuning, with `L₁ ≠ 0`, the output power passes through the primary flux:
`−Re(V₂ Ī₂) = (ωM/L₁) Im(ψ₁ Ī₂) − R₂‖I₂‖²`. -/
@[tmio M, powerlib_domain] theorem outputPower_eq_flux₁ {V₁ V₂ I₁ I₂ : ℂ}
    (hL₁ : w.primary.L ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re =
      ω * w.M / w.primary.L * (w.flux₁ I₁ I₂ * conj I₂).im - w.secondary.R * normSq I₂ := by
  rw [outputPower_eq_mutual w ω h]
  have e : (w.flux₁ I₁ I₂ * conj I₂).im = w.primary.L * (I₁ * conj I₂).im := by
    simp only [Passive.Coupled.flux₁, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [e]
  field_simp

/-- `c Im(z ū) ≤ |c| ‖z‖ ‖u‖`. -/
@[tmio T, powerlib_foundation] private theorem mul_im_le (c : ℝ) (z u : ℂ) :
    c * (z * conj u).im ≤ |c| * ‖z‖ * ‖u‖ :=
  calc c * (z * conj u).im ≤ |c * (z * conj u).im| := le_abs_self _
    _ = |c| * |(z * conj u).im| := abs_mul _ _
    _ ≤ |c| * ‖z * conj u‖ := by gcongr; exact Complex.abs_im_le_norm _
    _ = |c| * ‖z‖ * ‖u‖ := by rw [norm_mul, Complex.norm_conj, mul_assoc]

/-- The matched-load bound: `|c| p x − R x² ≤ c²Ψ²/(4R)` for `R > 0`, `p² ≤ Ψ²`. -/
@[tmio T, powerlib_foundation] private theorem matched_le {c p x R Ψ : ℝ} (hR : 0 < R)
    (hp : p ^ 2 ≤ Ψ ^ 2) : |c| * p * x - R * x ^ 2 ≤ c ^ 2 * Ψ ^ 2 / (4 * R) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|c| * p - 2 * R * x), sq_abs c, mul_le_mul_of_nonneg_left hp (sq_nonneg c)]

/-- Under a secondary flux bound `‖ψ₂‖² ≤ Ψ₂²` every operating point, at every tuning and with any
primary and any bridge voltages, delivers at most `−Re(V₂ Ī₂) ≤ ω²Ψ₂²/(4R₂)`. -/
@[tmio M, powerlib_domain] theorem outputPower_le_secondaryFluxLimit {V₁ V₂ I₁ I₂ : ℂ} {Ψ₂ : ℝ}
    (hR₂ : 0 < w.secondary.R) (h : Driven w ω V₁ V₂ I₁ I₂)
    (hψ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    -(V₂ * conj I₂).re ≤ secondaryFluxLimit w ω Ψ₂ := by
  rw [outputPower_eq_flux₂ w ω h, secondaryFluxLimit, Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_eq_norm_sq] at hψ
  have := mul_im_le ω (w.flux₂ I₁ I₂) I₂
  have := matched_le (c := ω) (x := ‖I₂‖) hR₂ hψ
  linarith

/-- Under a primary flux bound `‖ψ₁‖² ≤ Ψ₁²` every operating point, at every tuning and with any
bridge voltages, delivers at most `−Re(V₂ Ī₂) ≤ (ωM)²Ψ₁²/(4L₁²R₂)` (`L₁ ≠ 0`). -/
@[tmio M, powerlib_domain] theorem outputPower_le_primaryFluxLimit {V₁ V₂ I₁ I₂ : ℂ} {Ψ₁ : ℝ}
    (hL₁ : w.primary.L ≠ 0) (hR₂ : 0 < w.secondary.R) (h : Driven w ω V₁ V₂ I₁ I₂)
    (hψ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2) :
    -(V₂ * conj I₂).re ≤ primaryFluxLimit w ω Ψ₁ := by
  rw [outputPower_eq_flux₁ w ω hL₁ h, Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_eq_norm_sq] at hψ
  have e : primaryFluxLimit w ω Ψ₁ =
      (ω * w.M / w.primary.L) ^ 2 * Ψ₁ ^ 2 / (4 * w.secondary.R) := by
    rw [primaryFluxLimit]
    field_simp
  have := mul_im_le (ω * w.M / w.primary.L) (w.flux₁ I₁ I₂) I₂
  have := matched_le (c := ω * w.M / w.primary.L) (x := ‖I₂‖) hR₂ hψ
  rw [e]
  linarith

/-- The secondary flux limit is exact: with `R₂ > 0` and `M ≠ 0`, `ω²Ψ₂²/(4R₂)` is the greatest
`−Re(V₂ Ī₂)` over all operating points with `‖ψ₂‖² ≤ Ψ₂²`, at every tuning, with any primary and
without bridge limits. It is attained at `ψ₂ = Ψ₂`, `I₂ = −j ωΨ₂/(2R₂)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_secondaryFluxLimit {Ψ₂ : ℝ}
    (hR₂ : 0 < w.secondary.R) (hM : w.M ≠ 0) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = -(V₂ * conj I₂).re}
      (secondaryFluxLimit w ω Ψ₂) := by
  constructor
  · have hM' : (w.M : ℂ) ≠ 0 := by exact_mod_cast hM
    set I₂ : ℂ := I * ((-(ω * Ψ₂ / (2 * w.secondary.R)) : ℝ) : ℂ)
    set I₁ : ℂ := ((Ψ₂ : ℂ) - w.secondary.L * I₂) / w.M
    have hψ : w.flux₂ I₁ I₂ = Ψ₂ := by
      rw [Passive.Coupled.flux₂, mul_div_cancel₀ _ hM']
      ring
    have hd := (driven_iff w ω _ _ I₁ I₂).mpr ⟨rfl, rfl⟩
    refine ⟨_, _, I₁, I₂, hd, by rw [hψ, Complex.normSq_ofReal, sq], ?_⟩
    rw [outputPower_eq_flux₂ w ω hd, hψ, secondaryFluxLimit]
    simp only [I₂, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  · rintro P ⟨V₁, V₂, I₁, I₂, h, hψ, rfl⟩
    exact outputPower_le_secondaryFluxLimit w ω hR₂ h hψ

/-- The primary flux limit is exact: with `L₁ ≠ 0` and `R₂ > 0`, `(ωM)²Ψ₁²/(4L₁²R₂)` is the
greatest `−Re(V₂ Ī₂)` over all operating points with `‖ψ₁‖² ≤ Ψ₁²`, at every tuning and without
bridge limits. It is attained at `ψ₁ = Ψ₁`, `I₂ = −j ωMΨ₁/(2L₁R₂)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_primaryFluxLimit {Ψ₁ : ℝ}
    (hL₁ : w.primary.L ≠ 0) (hR₂ : 0 < w.secondary.R) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = -(V₂ * conj I₂).re}
      (primaryFluxLimit w ω Ψ₁) := by
  constructor
  · have hL₁' : (w.primary.L : ℂ) ≠ 0 := by exact_mod_cast hL₁
    set I₂ : ℂ := I * ((-(ω * w.M * Ψ₁ / (2 * w.primary.L * w.secondary.R)) : ℝ) : ℂ)
    set I₁ : ℂ := ((Ψ₁ : ℂ) - w.M * I₂) / w.primary.L
    have hψ : w.flux₁ I₁ I₂ = Ψ₁ := by
      rw [Passive.Coupled.flux₁, mul_div_cancel₀ _ hL₁']
      ring
    have hd := (driven_iff w ω _ _ I₁ I₂).mpr ⟨rfl, rfl⟩
    refine ⟨_, _, I₁, I₂, hd, by rw [hψ, Complex.normSq_ofReal, sq], ?_⟩
    rw [outputPower_eq_flux₁ w ω hL₁ hd, hψ, primaryFluxLimit]
    simp only [I₂, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  · rintro P ⟨V₁, V₂, I₁, I₂, h, hψ, rfl⟩
    exact outputPower_le_primaryFluxLimit w ω hL₁ hR₂ h hψ

/-! ## Bridges and a flux bound together -/

/-- Under the bridges and a secondary flux bound the resonant link (`R₁ > 0`, `R₂ > 0`) delivers
at most the smaller limit: `−Re(V₂ Ī₂) ≤ min(outputLimit, ω²Ψ₂²/(4R₂))`. -/
@[tmio M, powerlib_domain] theorem outputPower_le_min_secondaryFluxLimit {V₁ V₂ I₁ I₂ : ℂ}
    {ρ₁ ρ₂ Ψ₂ : ℝ} (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hR₂ : 0 < w.secondary.R) (h : Driven w ω V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) (hψ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    -(V₂ * conj I₂).re ≤ min (outputLimit w ω ρ₁ ρ₂) (secondaryFluxLimit w ω Ψ₂) := by
  have hΔ : 0 < determinant w ω := by
    unfold determinant
    positivity
  exact le_min (outputPower_le w ω hX₁ hX₂ hR₁ hΔ h h₁ h₂)
    (outputPower_le_secondaryFluxLimit w ω hR₂ h hψ)

/-- Under the bridges and a primary flux bound the resonant link (`R₁ > 0`, `R₂ > 0`, `L₁ ≠ 0`)
delivers at most the smaller limit: `−Re(V₂ Ī₂) ≤ min(outputLimit, (ωM)²Ψ₁²/(4L₁²R₂))`. -/
@[tmio M, powerlib_domain] theorem outputPower_le_min_primaryFluxLimit {V₁ V₂ I₁ I₂ : ℂ}
    {ρ₁ ρ₂ Ψ₁ : ℝ} (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hR₂ : 0 < w.secondary.R) (hL₁ : w.primary.L ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2) :
    -(V₂ * conj I₂).re ≤ min (outputLimit w ω ρ₁ ρ₂) (primaryFluxLimit w ω Ψ₁) := by
  have hΔ : 0 < determinant w ω := by
    unfold determinant
    positivity
  exact le_min (outputPower_le w ω hX₁ hX₂ hR₁ hΔ h h₁ h₂)
    (outputPower_le_primaryFluxLimit w ω hL₁ hR₂ h hψ)

/-- The currents at the bridge optimum `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)`: `I₁ = (R₂ρ₁ + |ωM|v⋆)/Δ`
is real and `I₂ = j (R₁v⋆ sgn(ωM) − ωMρ₁)/Δ` imaginary. -/
@[tmio M, powerlib_domain] private theorem currents_at_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    I₁ = (((w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂) / determinant w ω : ℝ) :
        ℂ) ∧
      I₂ = I * (((w.primary.R * optimalVoltage w ω ρ₁ ρ₂ * (ω * w.M / |ω * w.M|) -
        ω * w.M * ρ₁) / determinant w ω : ℝ) : ℂ) := by
  have hs : ω * w.M * (ω * w.M / |ω * w.M|) = |ω * w.M| := by
    rw [← mul_div_assoc, ← abs_mul_abs_self, mul_self_div_self]
  obtain ⟨e1, e2⟩ := currents_eq w ω hX₁ hX₂ hΔ h
  constructor
  · rw [e1]
    apply Complex.ext
    · simp only [Complex.div_ofReal_re, optimalPhasor, Complex.sub_re, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      congr 1
      linear_combination optimalVoltage w ω ρ₁ ρ₂ * hs
    · simp only [Complex.div_ofReal_im, optimalPhasor, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  · rw [e2]
    apply Complex.ext
    · simp only [Complex.div_ofReal_re, optimalPhasor, Complex.sub_re, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.div_ofReal_im, optimalPhasor, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring

/-- `((R₁v sgn(ωM) − ωMρ₁)/Δ)² = ((|ωM|ρ₁ − R₁v)/Δ)²`. -/
@[tmio M, powerlib_domain] private theorem sq_current₂_at_optimum {ρ₁ v : ℝ}
    (hm : ω * w.M ≠ 0) :
    ((w.primary.R * v * (ω * w.M / |ω * w.M|) - ω * w.M * ρ₁) / determinant w ω) ^ 2 =
      ((|ω * w.M| * ρ₁ - w.primary.R * v) / determinant w ω) ^ 2 := by
  have hs : ω * w.M * (ω * w.M / |ω * w.M|) = |ω * w.M| := by
    rw [← mul_div_assoc, ← abs_mul_abs_self, mul_self_div_self]
  have hs2 : (ω * w.M / |ω * w.M|) ^ 2 = 1 := by
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 hm)]
  rw [div_pow, div_pow]
  congr 1
  linear_combination (w.primary.R * v) ^ 2 * hs2 - 2 * w.primary.R * v * ρ₁ * hs -
    ρ₁ ^ 2 * sq_abs (ω * w.M)

/-- The primary flux at the bridge optimum `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)`:
`‖ψ₁‖² = (L₁²(R₂ρ₁ + |ωM|v⋆)² + M²(|ωM|ρ₁ − R₁v⋆)²)/Δ²`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₁_at_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    normSq (w.flux₁ I₁ I₂) = (w.primary.L ^ 2 *
        (w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂) ^ 2 +
      w.M ^ 2 * (|ω * w.M| * ρ₁ - w.primary.R * optimalVoltage w ω ρ₁ ρ₂) ^ 2) /
        determinant w ω ^ 2 := by
  obtain ⟨e1, e2⟩ := currents_at_optimum w ω hX₁ hX₂ hΔ h
  have hb := sq_current₂_at_optimum w ω (ρ₁ := ρ₁) (v := optimalVoltage w ω ρ₁ ρ₂) hm
  rw [e1, e2, Passive.Coupled.flux₁]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination w.M ^ 2 * hb

/-- The secondary flux at the bridge optimum `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)`:
`‖ψ₂‖² = (M²(R₂ρ₁ + |ωM|v⋆)² + L₂²(|ωM|ρ₁ − R₁v⋆)²)/Δ²`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₂_at_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    normSq (w.flux₂ I₁ I₂) = (w.M ^ 2 *
        (w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂) ^ 2 +
      w.secondary.L ^ 2 * (|ω * w.M| * ρ₁ - w.primary.R * optimalVoltage w ω ρ₁ ρ₂) ^ 2) /
        determinant w ω ^ 2 := by
  obtain ⟨e1, e2⟩ := currents_at_optimum w ω hX₁ hX₂ hΔ h
  have hb := sq_current₂_at_optimum w ω (ρ₁ := ρ₁) (v := optimalVoltage w ω ρ₁ ρ₂) hm
  rw [e1, e2, Passive.Coupled.flux₂]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination w.secondary.L ^ 2 * hb

@[tmio M, powerlib_domain] private theorem optimum_mem {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ‖(ρ₁ : ℂ)‖ ≤ ρ₁ ∧ ‖optimalPhasor w ω ρ₁ ρ₂‖ ≤ ρ₂ ∧
      Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂)
        ((w.secondary.R * (ρ₁ : ℂ) - ((ω * w.M : ℝ) : ℂ) * I * optimalPhasor w ω ρ₁ ρ₂) /
          (determinant w ω : ℂ))
        ((w.primary.R * optimalPhasor w ω ρ₁ ρ₂ - ((ω * w.M : ℝ) : ℂ) * I * (ρ₁ : ℂ)) /
          (determinant w ω : ℂ)) ∧
      outputLimit w ω ρ₁ ρ₂ = -(optimalPhasor w ω ρ₁ ρ₂ *
        conj ((w.primary.R * optimalPhasor w ω ρ₁ ρ₂ - ((ω * w.M : ℝ) : ℂ) * I * (ρ₁ : ℂ)) /
          (determinant w ω : ℂ))).re := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hv0 : 0 ≤ optimalVoltage w ω ρ₁ ρ₂ := le_min hρ₂ (by positivity)
  have hd := driven_currents w ω (ρ₁ : ℂ) (optimalPhasor w ω ρ₁ ρ₂) hX₁ hX₂ hΔ.ne'
  refine ⟨?_, ?_, hd, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₁]
  · rw [optimalPhasor, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_div, abs_abs, div_self hma.ne', mul_one, abs_of_nonneg hv0]
    exact min_le_left _ _
  · rw [outputPower_optimum w ω hX₁ hX₂ hΔ.ne' hm hd, outputLimit_eq w ω hR₁]

/-- The bridge limit is exact under a primary flux bound when the flux at the bridge optimum
meets it: if `L₁²(R₂ρ₁ + |ωM|v⋆)² + M²(|ωM|ρ₁ − R₁v⋆)² ≤ Ψ₁²Δ²`, then `outputLimit` is the
greatest `−Re(V₂ Ī₂)` over the operating points with `‖V_k‖ ≤ ρ_k` and `‖ψ₁‖² ≤ Ψ₁²`. -/
@[tmio M, powerlib_domain] theorem isGreatest_outputLimit_flux₁ {ρ₁ ρ₂ Ψ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hψ : w.primary.L ^ 2 * (w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂) ^ 2 +
      w.M ^ 2 * (|ω * w.M| * ρ₁ - w.primary.R * optimalVoltage w ω ρ₁ ρ₂) ^ 2 ≤
        Ψ₁ ^ 2 * determinant w ω ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = -(V₂ * conj I₂).re} (outputLimit w ω ρ₁ ρ₂) := by
  constructor
  · obtain ⟨h₁, h₂, hd, hP⟩ := optimum_mem w ω hX₁ hX₂ hR₁ hΔ hm hρ₁ hρ₂
    refine ⟨_, _, _, _, h₁, h₂, hd, ?_, hP⟩
    rw [normSq_flux₁_at_optimum w ω hX₁ hX₂ hΔ.ne' hm hd, div_le_iff₀ (by positivity)]
    exact hψ
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, -, rfl⟩
    exact outputPower_le w ω hX₁ hX₂ hR₁ hΔ h h₁ h₂

/-- The bridge limit is exact under a secondary flux bound when the flux at the bridge optimum
meets it: if `M²(R₂ρ₁ + |ωM|v⋆)² + L₂²(|ωM|ρ₁ − R₁v⋆)² ≤ Ψ₂²Δ²`, then `outputLimit` is the
greatest `−Re(V₂ Ī₂)` over the operating points with `‖V_k‖ ≤ ρ_k` and `‖ψ₂‖² ≤ Ψ₂²`. -/
@[tmio M, powerlib_domain] theorem isGreatest_outputLimit_flux₂ {ρ₁ ρ₂ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hψ : w.M ^ 2 * (w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂) ^ 2 +
      w.secondary.L ^ 2 * (|ω * w.M| * ρ₁ - w.primary.R * optimalVoltage w ω ρ₁ ρ₂) ^ 2 ≤
        Ψ₂ ^ 2 * determinant w ω ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = -(V₂ * conj I₂).re} (outputLimit w ω ρ₁ ρ₂) := by
  constructor
  · obtain ⟨h₁, h₂, hd, hP⟩ := optimum_mem w ω hX₁ hX₂ hR₁ hΔ hm hρ₁ hρ₂
    refine ⟨_, _, _, _, h₁, h₂, hd, ?_, hP⟩
    rw [normSq_flux₂_at_optimum w ω hX₁ hX₂ hΔ.ne' hm hd, div_le_iff₀ (by positivity)]
    exact hψ
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, -, rfl⟩
    exact outputPower_le w ω hX₁ hX₂ hR₁ hΔ h h₁ h₂

/-- `‖z‖ ≤ ρ` from `c²‖z‖² = A ≤ (cρ)²`, `c ≠ 0`, `ρ ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem norm_le_of_scaled {z : ℂ} {c ρ A : ℝ}
    (hc : c ≠ 0) (hρ : 0 ≤ ρ) (hz : c ^ 2 * normSq z = A) (hA : A ≤ (c * ρ) ^ 2) : ‖z‖ ≤ ρ := by
  have hk : 0 < c ^ 2 := by positivity
  rw [mul_pow] at hA
  have h1 : normSq z ≤ ρ ^ 2 := le_of_mul_le_mul_left ((le_of_eq hz).trans hA) hk
  rw [← Complex.sq_norm] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ two_ne_zero).mp h1

/-- The secondary flux limit is exact under the bridges when the bridge voltages of the
flux optimizer fit them: on the resonant link with `R₂ > 0`, `M ≠ 0`, `ρ_k ≥ 0`, if
`Ψ₂²((2R₁R₂ + (ωM)²)² + (ωR₁L₂)²) ≤ (2R₂Mρ₁)²` and `(ωΨ₂)²(R₂² + (ωL₂)²) ≤ (2R₂ρ₂)²`, then
`ω²Ψ₂²/(4R₂)` is the greatest `−Re(V₂ Ī₂)` over the operating points with `‖V_k‖ ≤ ρ_k` and
`‖ψ₂‖² ≤ Ψ₂²`. -/
@[tmio M, powerlib_domain] theorem isGreatest_secondaryFluxLimit_bridges {ρ₁ ρ₂ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₂ : 0 < w.secondary.R) (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hV₁ : Ψ₂ ^ 2 * ((2 * w.primary.R * w.secondary.R + (ω * w.M) ^ 2) ^ 2 +
      (ω * w.primary.R * w.secondary.L) ^ 2) ≤ (2 * w.secondary.R * w.M * ρ₁) ^ 2)
    (hV₂ : (ω * Ψ₂) ^ 2 * (w.secondary.R ^ 2 + (ω * w.secondary.L) ^ 2) ≤
      (2 * w.secondary.R * ρ₂) ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = -(V₂ * conj I₂).re}
      (secondaryFluxLimit w ω Ψ₂) := by
  constructor
  · obtain ⟨c, hc⟩ : ∃ c, c = ω * Ψ₂ / (2 * w.secondary.R) := ⟨_, rfl⟩
    obtain ⟨I₂, hI₂⟩ : ∃ z : ℂ, z = I * ((-c : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨I₁, hI₁⟩ : ∃ z : ℂ,
        z = ((Ψ₂ / w.M : ℝ) : ℂ) + I * ((w.secondary.L * c / w.M : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨V₁, hV₁d⟩ : ∃ z : ℂ, z = ((w.primary.R * Ψ₂ / w.M + ω * w.M * c : ℝ) : ℂ) +
        I * ((w.primary.R * w.secondary.L * c / w.M : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨V₂, hV₂d⟩ : ∃ z : ℂ, z = ((-(ω * w.secondary.L * c) : ℝ) : ℂ) +
        I * ((ω * Ψ₂ - w.secondary.R * c : ℝ) : ℂ) := ⟨_, rfl⟩
    have hd : Driven w ω V₁ V₂ I₁ I₂ := by
      rw [driven_iff, hX₁, hX₂, hV₁d, hV₂d, hI₁, hI₂]
      constructor <;> apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
        field_simp <;> ring
    have hψ : w.flux₂ I₁ I₂ = Ψ₂ := by
      rw [Passive.Coupled.flux₂, hI₁, hI₂]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
        field_simp <;> ring
    refine ⟨V₁, V₂, I₁, I₂, ?_, ?_, hd, by rw [hψ, Complex.normSq_ofReal, sq], ?_⟩
    · refine norm_le_of_scaled (c := 2 * w.secondary.R * w.M) (by positivity) hρ₁ ?_ hV₁
      rw [hV₁d, hc]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    · refine norm_le_of_scaled (c := 2 * w.secondary.R) (by positivity) hρ₂ ?_ hV₂
      rw [hV₂d, hc]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    · rw [outputPower_eq_flux₂ w ω hd, hψ, hI₂, hc, secondaryFluxLimit]
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
  · rintro P ⟨V₁, V₂, I₁, I₂, -, -, h, hψ, rfl⟩
    exact outputPower_le_secondaryFluxLimit w ω hR₂ h hψ

/-- The primary flux limit is exact under the bridges when the bridge voltages of the flux
optimizer fit them: on the resonant link with `L₁ ≠ 0`, `R₂ > 0`, `ρ_k ≥ 0`, if
`Ψ₁²((L₁(2R₁R₂ + (ωM)²))² + (ωR₁M²)²) ≤ (2L₁²R₂ρ₁)²` and
`(ωMΨ₁)²((ωM²)² + (L₁R₂)²) ≤ (2L₁²R₂ρ₂)²`, then `(ωM)²Ψ₁²/(4L₁²R₂)` is the greatest
`−Re(V₂ Ī₂)` over the operating points with `‖V_k‖ ≤ ρ_k` and `‖ψ₁‖² ≤ Ψ₁²`. -/
@[tmio M, powerlib_domain] theorem isGreatest_primaryFluxLimit_bridges {ρ₁ ρ₂ Ψ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hL₁ : w.primary.L ≠ 0) (hR₂ : 0 < w.secondary.R) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hV₁ : Ψ₁ ^ 2 * ((w.primary.L * (2 * w.primary.R * w.secondary.R + (ω * w.M) ^ 2)) ^ 2 +
      (ω * w.primary.R * w.M ^ 2) ^ 2) ≤ (2 * w.primary.L ^ 2 * w.secondary.R * ρ₁) ^ 2)
    (hV₂ : (ω * w.M * Ψ₁) ^ 2 * ((ω * w.M ^ 2) ^ 2 + (w.primary.L * w.secondary.R) ^ 2) ≤
      (2 * w.primary.L ^ 2 * w.secondary.R * ρ₂) ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = -(V₂ * conj I₂).re}
      (primaryFluxLimit w ω Ψ₁) := by
  constructor
  · obtain ⟨c, hc⟩ : ∃ c, c = ω * w.M * Ψ₁ / (2 * w.primary.L * w.secondary.R) := ⟨_, rfl⟩
    obtain ⟨I₂, hI₂⟩ : ∃ z : ℂ, z = I * ((-c : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨I₁, hI₁⟩ : ∃ z : ℂ,
        z = ((Ψ₁ / w.primary.L : ℝ) : ℂ) + I * ((w.M * c / w.primary.L : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨V₁, hV₁d⟩ : ∃ z : ℂ,
        z = ((w.primary.R * Ψ₁ / w.primary.L + ω * w.M * c : ℝ) : ℂ) +
          I * ((w.primary.R * w.M * c / w.primary.L : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨V₂, hV₂d⟩ : ∃ z : ℂ, z = ((-(ω * w.M * w.M * c / w.primary.L) : ℝ) : ℂ) +
        I * ((ω * w.M * Ψ₁ / w.primary.L - w.secondary.R * c : ℝ) : ℂ) := ⟨_, rfl⟩
    have hd : Driven w ω V₁ V₂ I₁ I₂ := by
      rw [driven_iff, hX₁, hX₂, hV₁d, hV₂d, hI₁, hI₂]
      constructor <;> apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
        field_simp <;> ring
    have hψ : w.flux₁ I₁ I₂ = Ψ₁ := by
      rw [Passive.Coupled.flux₁, hI₁, hI₂]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
        field_simp <;> ring
    refine ⟨V₁, V₂, I₁, I₂, ?_, ?_, hd, by rw [hψ, Complex.normSq_ofReal, sq], ?_⟩
    · refine norm_le_of_scaled (c := 2 * w.primary.L ^ 2 * w.secondary.R) (by positivity) hρ₁
        ?_ hV₁
      rw [hV₁d, hc]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    · refine norm_le_of_scaled (c := 2 * w.primary.L ^ 2 * w.secondary.R) (by positivity) hρ₂
        ?_ hV₂
      rw [hV₂d, hc]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    · rw [outputPower_eq_flux₁ w ω hL₁ hd, hψ, hI₂, hc, primaryFluxLimit]
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
  · rintro P ⟨V₁, V₂, I₁, I₂, -, -, h, hψ, rfl⟩
    exact outputPower_le_primaryFluxLimit w ω hL₁ hR₂ h hψ

end powerlib.WPT.LossyFlux
