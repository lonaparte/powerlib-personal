import theorem.GridTiedConverter.GFM.Tracking.Linear
import theorem.SpecialFunctions.Elementary

/-! # Grid-forming frequency following: bandwidth, phase, ROCOF and the power filter

Exact frequency-response identities of the GFM synchronization transfer, the counterparts of the
SRF-PLL meter identities of `theorem/GridTiedConverter/PLL/Measurement.lean`.

Model boundary.
* System: the linearized reduced GFM of `theorem/GridTiedConverter/GFM/Tracking/Linear.lean`
  (two-state loop `θ̇ = Δω`, `M Δω̇ = P_ref − P_e(θ − θ_g) − D Δω` at the power angle `δ`,
  transfer `H(s) = K/(M s² + D s + K)` from grid angle to converter angle and from grid frequency
  to converter frequency, `K = P_e'(δ)`), with the boundary stated there (quasi-static line,
  constant `E`, no inner loops, delay or PWM; continuous time). Natural frequency
  `ω_n = √(K/M)` and damping ratio `ζ = D/(2√(MK))` are those of the Jacobian
  (`Criteria.naturalFrequency`, `Criteria.dampingRatio`).
* Power filter: the first-order filter `Ṗ_f = ω_c (P_e − P_f)` of the three-state loop
  (`VSMLPF.field`, third row) as a one-state plant with input `P_e`; a double-frequency ripple
  `P_e = R cos(2ω₀ t)` (e.g. from a negative-sequence grid voltage) is a given input signal, its
  origin is not modelled here.

Source: GFM counterpart study note t8 (tracking): derivation with the SymPy/SciPy checks
`s2_frequency_response.py`, `s4_filter.py` (outside the repository); Ogata, *Modern Control
Engineering* (5th ed. 2010) §5-3, §7-2 (second-order low-pass: resonance, bandwidth).

Results.
* `|H(jω)|² = K²/((K − Mω²)² + (Dω)²)` (`normSq_transferFn`). −3 dB bandwidth: for `M, K > 0`
  and `ω ≥ 0`, `|H(jω)|² = 1/2` exactly at `ω_b = ω_n √(1 − 2ζ² + √((1 − 2ζ²)² + 1))`
  (`normSq_transferFn_eq_half_iff`; the pure second-order low-pass formula, which the PLL note
  wrongly used for the PLL), `|H|² > 1/2` below and `< 1/2` above (`D ≠ 0`,
  `normSq_transferFn_cmp_half`).
* Phase: `arg H(jω) = −π/2 + arctan((K − Mω²)/(Dω))` for `D, K, ω > 0`, at every frequency
  (`arg_transferFn`); exactly `−π/2` at `ω_n` (`arg_transferFn_naturalFrequency`).
* No amplification: `|H(jω)| ≤ 1` at every `ω` iff `ζ² ≥ 1/2` (`M, K > 0`,
  `normSq_transferFn_le_one_iff`); below that damping the converter frequency amplifies a band
  of grid-frequency oscillations.
* ROCOF: the derivative-output model `rocofPlant` (`LTI.derivModel` of the frequency channel)
  has transfer `s H(s)` (`transfer_rocofPlant`; three states: `transfer_filterRocofPlant`),
  `|jω H(jω)|² = ω² |H(jω)|²` (`normSq_rocof`), and its gain never exceeds `K/D`
  (`normSq_rocof_le`), with equality at `ω_n` (`normSq_rocof_naturalFrequency`).
* Power filter: `F(s) = ω_c/(s + ω_c)` (`transfer_powerFilterPlant`),
  `|F(2jω₀)|² = ω_c²/(ω_c² + 4ω₀²)` (`normSq_powerFilter_ripple`), and the forced ripple
  `R (ω_c² cos 2ω₀t + 2ω₀ω_c sin 2ω₀t)/(ω_c² + 4ω₀²) = R Re(F(2jω₀) e^{2jω₀t})` is a trajectory
  (`rippleResponse_isTrajectory`, `rippleResponse_eq`).

Family and connection conclusions.
No family and no connection conclusion: every result is a frequency-response identity on the
plants, not a behaviour of a family's models.

No GFM counterpart of the PLL signal layer (`theorem/GridTiedConverter/PLL/Signals.lean`): the
phase detector, the DDSRF decoupling, the SOGI quadrature generator and the moving-average filter
act on the measured grid voltage to extract its phase. The grid-forming converter does not
measure the grid phase; it measures its own active power and synchronizes through the power loop,
so its only measurement filter is the power filter treated here.
-/

noncomputable section
namespace powerlib.GFM.Tracking
open Matrix Complex
open powerlib.Synchronous (SwingParams)

/-! ## Magnitude and the −3 dB bandwidth -/

/-- `|H(jω)|² = K²/((K − Mω²)² + (Dω)²)`. -/
@[tmio M, powerlib_domain] theorem normSq_transferFn (p : SwingParams) (δ ω : ℝ) :
    normSq (transferFn p δ ((ω : ℂ) * I)) =
      p.syncCoeff δ ^ 2 / ((p.syncCoeff δ - p.M * ω ^ 2) ^ 2 + (p.D * ω) ^ 2) := by
  have hden : (p.M : ℂ) * ((ω : ℂ) * I) ^ 2 + (p.D : ℂ) * ((ω : ℂ) * I) + (p.syncCoeff δ : ℂ) =
      ⟨p.syncCoeff δ - p.M * ω ^ 2, p.D * ω⟩ := by
    apply Complex.ext <;> simp [pow_two]; ring
  rw [transferFn, hden, Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_mk]
  ring

/-- The `M`-normalized form `b²/((b − ω²)² + (aω)²)`, `a = D/M`, `b = K/M`. -/
@[tmio M, powerlib_domain] private lemma normSq_transferFn_ab (p : SwingParams) {δ : ℝ}
    (hM : p.M ≠ 0) (ω : ℝ) :
    normSq (transferFn p δ ((ω : ℂ) * I)) =
      (p.syncCoeff δ / p.M) ^ 2 /
        ((p.syncCoeff δ / p.M - ω ^ 2) ^ 2 + (p.D / p.M * ω) ^ 2) := by
  rw [normSq_transferFn]
  have h1 : (p.syncCoeff δ / p.M - ω ^ 2) ^ 2 + (p.D / p.M * ω) ^ 2 =
      ((p.syncCoeff δ - p.M * ω ^ 2) ^ 2 + (p.D * ω) ^ 2) / p.M ^ 2 := by
    field_simp
  rw [h1, div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 hM)]

/-- The exact −3 dB bandwidth of a second-order low-pass `ω_n²/(s² + 2ζω_n s + ω_n²)`:
`ω_n √(1 − 2ζ² + √((1 − 2ζ²)² + 1))`. -/
def lowPassBandwidth (ωn ζ : ℝ) : ℝ :=
  ωn * Real.sqrt (1 - 2 * ζ ^ 2 + Real.sqrt ((1 - 2 * ζ ^ 2) ^ 2 + 1))

/-- The squared bandwidth `X` is positive and a root of `X² + (a² − 2b) X − b²`, where
`b = ω_n² > 0`, `a = 2ζω_n`. -/
@[tmio T, powerlib_foundation] private lemma lowPassBandwidth_sq {a b ωn ζ : ℝ} (hb : 0 < b)
    (hn : ωn ^ 2 = b) (hz : 2 * ζ * ωn = a) :
    0 < lowPassBandwidth ωn ζ ^ 2 ∧
      (lowPassBandwidth ωn ζ ^ 2) ^ 2 + (a ^ 2 - 2 * b) * lowPassBandwidth ωn ζ ^ 2 -
        b ^ 2 = 0 := by
  set r := Real.sqrt ((1 - 2 * ζ ^ 2) ^ 2 + 1) with hr
  have hr2 : r ^ 2 = (1 - 2 * ζ ^ 2) ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hin : 0 < 1 - 2 * ζ ^ 2 + r := by nlinarith
  have hX : lowPassBandwidth ωn ζ ^ 2 = ωn ^ 2 * (1 - 2 * ζ ^ 2 + r) := by
    rw [lowPassBandwidth, mul_pow, Real.sq_sqrt hin.le]
  have hn0 : 0 < ωn ^ 2 := by rw [hn]; exact hb
  refine ⟨by rw [hX]; positivity, ?_⟩
  rw [hX, ← hn, ← hz]
  linear_combination ωn ^ 4 * hr2

/-- `2b² − ((b − ω²)² + (aω)²) = −(ω² − X)(ω² + b²/X)` at a positive root `X` of
`X² + (a² − 2b)X − b²`. -/
@[tmio T, powerlib_foundation] private lemma lowPass_factor {a b X : ℝ} (hX : 0 < X)
    (hroot : X ^ 2 + (a ^ 2 - 2 * b) * X - b ^ 2 = 0) (ω : ℝ) :
    2 * b ^ 2 - ((b - ω ^ 2) ^ 2 + (a * ω) ^ 2) = -((ω ^ 2 - X) * (ω ^ 2 + b ^ 2 / X)) := by
  have hdiv : b ^ 2 / X = X + (a ^ 2 - 2 * b) := by
    rw [div_eq_iff hX.ne']; linear_combination -hroot
  rw [hdiv]
  linear_combination -hroot

/-- The denominator `(b − ω²)² + (aω)²` vanishes only at `ω² = b` with `a = 0` (`b > 0`). -/
@[tmio T, powerlib_foundation] private lemma lowPass_den {a b : ℝ} (hb : 0 < b) (ω : ℝ) :
    0 < (b - ω ^ 2) ^ 2 + (a * ω) ^ 2 ∨ (ω ^ 2 = b ∧ a = 0) := by
  rcases (add_nonneg (sq_nonneg (b - ω ^ 2)) (sq_nonneg (a * ω))).lt_or_eq with h | h
  · exact Or.inl h
  · right
    have h1 : b - ω ^ 2 = 0 := by nlinarith [sq_nonneg (b - ω ^ 2), sq_nonneg (a * ω)]
    have h2 : a * ω = 0 := by nlinarith [sq_nonneg (b - ω ^ 2), sq_nonneg (a * ω)]
    have hω : ω ≠ 0 := by rintro rfl; simp at h1; linarith
    exact ⟨by linarith, (mul_eq_zero.mp h2).resolve_right hω⟩

/-- The normalized data of the Jacobian: `ω_n² = K/M`, `2ζω_n = D/M` (`M, K > 0`). -/
@[tmio M, powerlib_domain] private lemma jacobian_data (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hK : 0 < p.syncCoeff δ) :
    Criteria.naturalFrequency (p.jacobian δ) ^ 2 = p.syncCoeff δ / p.M ∧
      2 * Criteria.dampingRatio (p.jacobian δ) * Criteria.naturalFrequency (p.jacobian δ) =
        p.D / p.M := by
  have hdet : 0 < (p.jacobian δ).det := by rw [SwingParams.det_jacobian]; positivity
  refine ⟨by rw [Criteria.naturalFrequency_sq _ hdet.le, SwingParams.det_jacobian], ?_⟩
  rw [Criteria.two_mul_dampingRatio_mul_naturalFrequency _ hdet, SwingParams.trace_jacobian]
  ring

/-- −3 dB bandwidth of the GFM synchronization: for `M, K > 0` and `ω ≥ 0`,
`|H(jω)|² = 1/2 ⇔ ω = ω_n √(1 − 2ζ² + √((1 − 2ζ²)² + 1))`. -/
@[tmio M, powerlib_domain] theorem normSq_transferFn_eq_half_iff (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hK : 0 < p.syncCoeff δ) {ω : ℝ} (hω : 0 ≤ ω) :
    normSq (transferFn p δ ((ω : ℂ) * I)) = 1 / 2 ↔
      ω = lowPassBandwidth (Criteria.naturalFrequency (p.jacobian δ))
        (Criteria.dampingRatio (p.jacobian δ)) := by
  obtain ⟨hn, hz⟩ := jacobian_data p hM hK
  have hb : 0 < p.syncCoeff δ / p.M := by positivity
  obtain ⟨hX, hroot⟩ := lowPassBandwidth_sq hb hn hz
  rw [normSq_transferFn_ab p hM.ne']
  set wb := lowPassBandwidth (Criteria.naturalFrequency (p.jacobian δ))
    (Criteria.dampingRatio (p.jacobian δ))
  have hwb : 0 ≤ wb := by
    simp only [wb, lowPassBandwidth, Criteria.naturalFrequency]; positivity
  set a := p.D / p.M
  set b := p.syncCoeff δ / p.M
  have hfac := lowPass_factor hX hroot ω
  have hpos : 0 < ω ^ 2 + b ^ 2 / wb ^ 2 := by positivity
  rcases lowPass_den (a := a) hb ω with hD | ⟨hω2, ha⟩
  · rw [div_eq_iff hD.ne']
    constructor
    · intro he
      have h0 : (ω ^ 2 - wb ^ 2) * (ω ^ 2 + b ^ 2 / wb ^ 2) = 0 := by linarith
      have hx : ω ^ 2 = wb ^ 2 := by
        have := (mul_eq_zero.mp h0).resolve_right hpos.ne'; linarith
      exact (pow_left_inj₀ hω hwb two_ne_zero).mp hx
    · intro he
      have h0 : 2 * b ^ 2 - ((b - ω ^ 2) ^ 2 + (a * ω) ^ 2) = 0 := by
        rw [hfac, he, sub_self, zero_mul, neg_zero]
      linarith
  · have hD0 : (b - ω ^ 2) ^ 2 + (a * ω) ^ 2 = 0 := by rw [hω2, ha]; ring
    rw [hD0, div_zero]
    constructor
    · intro h0; norm_num at h0
    · intro he
      exfalso
      have hXb : wb ^ 2 = b := by rw [← he, hω2]
      rw [hXb, ha] at hroot
      nlinarith

/-- Inside the bandwidth `|H(jω)|² > 1/2`, outside `|H(jω)|² < 1/2` (`M, K > 0`, `D ≠ 0`). -/
@[tmio M, powerlib_domain] theorem normSq_transferFn_cmp_half (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hK : 0 < p.syncCoeff δ) (hD : p.D ≠ 0) {ω : ℝ} (hω : 0 ≤ ω) :
    (ω < lowPassBandwidth (Criteria.naturalFrequency (p.jacobian δ))
        (Criteria.dampingRatio (p.jacobian δ)) →
      1 / 2 < normSq (transferFn p δ ((ω : ℂ) * I))) ∧
    (lowPassBandwidth (Criteria.naturalFrequency (p.jacobian δ))
        (Criteria.dampingRatio (p.jacobian δ)) < ω →
      normSq (transferFn p δ ((ω : ℂ) * I)) < 1 / 2) := by
  obtain ⟨hn, hz⟩ := jacobian_data p hM hK
  have hb : 0 < p.syncCoeff δ / p.M := by positivity
  obtain ⟨hX, hroot⟩ := lowPassBandwidth_sq hb hn hz
  rw [normSq_transferFn_ab p hM.ne']
  set wb := lowPassBandwidth (Criteria.naturalFrequency (p.jacobian δ))
    (Criteria.dampingRatio (p.jacobian δ))
  have hwb : 0 ≤ wb := by
    simp only [wb, lowPassBandwidth, Criteria.naturalFrequency]; positivity
  set a := p.D / p.M
  set b := p.syncCoeff δ / p.M
  have ha : a ≠ 0 := div_ne_zero hD hM.ne'
  have hfac := lowPass_factor hX hroot ω
  have hpos : 0 < ω ^ 2 + b ^ 2 / wb ^ 2 := by positivity
  have hden : 0 < (b - ω ^ 2) ^ 2 + (a * ω) ^ 2 := by
    rcases lowPass_den (a := a) hb ω with h | ⟨-, h⟩
    · exact h
    · exact absurd h ha
  constructor
  · intro hlt
    rw [lt_div_iff₀ hden]
    have : ω ^ 2 < wb ^ 2 := pow_lt_pow_left₀ hlt hω two_ne_zero
    nlinarith
  · intro hlt
    rw [div_lt_iff₀ hden]
    have : wb ^ 2 < ω ^ 2 := pow_lt_pow_left₀ hlt hwb two_ne_zero
    nlinarith

/-! ## Phase -/

/-- Phase of the GFM synchronization at every frequency: for `D, K, ω > 0`,
`arg H(jω) = −π/2 + arctan((K − Mω²)/(Dω))`. -/
@[tmio M, powerlib_domain] theorem arg_transferFn (p : SwingParams) {δ ω : ℝ} (hD : 0 < p.D)
    (hK : 0 < p.syncCoeff δ) (hω : 0 < ω) :
    arg (transferFn p δ ((ω : ℂ) * I)) =
      -(Real.pi / 2) + Real.arctan ((p.syncCoeff δ - p.M * ω ^ 2) / (p.D * ω)) := by
  set t := (p.syncCoeff δ - p.M * ω ^ 2) / (p.D * ω) with ht
  have hDω : 0 < p.D * ω := mul_pos hD hω
  set c := p.syncCoeff δ / (p.D * ω * (1 + t ^ 2)) with hc
  have hc0 : 0 < c := by positivity
  have hH : transferFn p δ ((ω : ℂ) * I) = (c : ℂ) * (-I * ⟨1, t⟩) := by
    have hden : (p.M : ℂ) * ((ω : ℂ) * I) ^ 2 + (p.D : ℂ) * ((ω : ℂ) * I) +
        (p.syncCoeff δ : ℂ) = ((p.D * ω : ℝ) : ℂ) * (I * ⟨1, -t⟩) := by
      apply Complex.ext <;> simp [pow_two, ht]
      field_simp
      ring
    have hne : ((p.D * ω : ℝ) : ℂ) * (I * ⟨1, -t⟩) ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast hDω.ne') (mul_ne_zero I_ne_zero ?_)
      intro h; have := congrArg Complex.re h; simp at this
    rw [transferFn, hden, div_eq_iff hne]
    have hprod : (c : ℂ) * (-I * ⟨1, t⟩) * (((p.D * ω : ℝ) : ℂ) * (I * ⟨1, -t⟩)) =
        ((c * (p.D * ω) * (1 + t * t) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    have hcK : c * (p.D * ω) * (1 + t * t) = p.syncCoeff δ := by
      rw [hc, show t * t = t ^ 2 by ring]; field_simp
    rw [hprod, hcK]
  have hw : (⟨1, t⟩ : ℂ) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
  have harg : arg (⟨1, t⟩ : ℂ) = Real.arctan t := by
    rw [SpecialFunctions.arg_eq_arctan (by simp)]; simp
  rw [hH, Complex.arg_real_mul _ hc0, Complex.arg_mul (neg_ne_zero.mpr I_ne_zero) hw,
    Complex.arg_neg_I, harg]
  rw [arg_neg_I, harg]
  have h1 := Real.neg_pi_div_two_lt_arctan t
  have h2 := Real.arctan_lt_pi_div_two t
  constructor <;> linarith [Real.pi_pos]

/-- At the natural frequency `ω_n = √(K/M)` the converter lags the grid by exactly a quarter
period, `arg H(jω_n) = −π/2` (`M, D, K > 0`). -/
@[tmio M, powerlib_domain] theorem arg_transferFn_naturalFrequency (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hD : 0 < p.D) (hK : 0 < p.syncCoeff δ) :
    arg (transferFn p δ ((Criteria.naturalFrequency (p.jacobian δ) : ℂ) * I)) =
      -(Real.pi / 2) := by
  obtain ⟨hn, -⟩ := jacobian_data p hM hK
  have hω : 0 < Criteria.naturalFrequency (p.jacobian δ) := by
    rw [naturalFrequency_jacobian]; exact Real.sqrt_pos.mpr (by positivity)
  rw [arg_transferFn p hD hK hω, hn, show p.syncCoeff δ - p.M * (p.syncCoeff δ / p.M) = 0 by
    field_simp; ring, zero_div, Real.arctan_zero, add_zero]

/-! ## No amplification -/

/-- `|H(jω)| ≤ 1` at every frequency iff `2MK ≤ D²` (`M, K > 0`). -/
@[tmio M, powerlib_domain] private lemma normSq_le_one_iff_aux (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) :
    (∀ ω : ℝ, normSq (transferFn p δ ((ω : ℂ) * I)) ≤ 1) ↔
      2 * p.M * p.syncCoeff δ ≤ p.D ^ 2 := by
  set K := p.syncCoeff δ
  constructor
  · intro h
    by_contra hc
    push Not at hc
    set e := 2 * p.M * K - p.D ^ 2 with he
    have he0 : 0 < e := by linarith
    set ω := Real.sqrt (e / (4 * p.M ^ 2)) with hωdef
    have hω2 : ω ^ 2 = e / (4 * p.M ^ 2) := Real.sq_sqrt (by positivity)
    have hgap : 0 < K - p.M * ω ^ 2 := by
      rw [hω2]
      have : p.M * (e / (4 * p.M ^ 2)) = e / (4 * p.M) := by field_simp
      rw [this, he]
      have : (2 * p.M * K - p.D ^ 2) / (4 * p.M) < K := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith [sq_nonneg p.D]
      linarith
    have hden : 0 < (K - p.M * ω ^ 2) ^ 2 + (p.D * ω) ^ 2 := by positivity
    have hlt : (K - p.M * ω ^ 2) ^ 2 + (p.D * ω) ^ 2 < K ^ 2 := by
      have hexp : (K - p.M * ω ^ 2) ^ 2 + (p.D * ω) ^ 2 =
          K ^ 2 + ω ^ 2 * (p.M ^ 2 * ω ^ 2 - e) := by rw [he]; ring
      have hω0 : 0 < ω ^ 2 := by rw [hω2]; positivity
      have : p.M ^ 2 * ω ^ 2 - e < 0 := by
        rw [hω2, show p.M ^ 2 * (e / (4 * p.M ^ 2)) = e / 4 by field_simp]; linarith
      rw [hexp]; nlinarith
    have := h ω
    rw [normSq_transferFn, div_le_one hden] at this
    linarith
  · intro h ω
    rw [normSq_transferFn]
    rcases (add_nonneg (sq_nonneg (K - p.M * ω ^ 2)) (sq_nonneg (p.D * ω))).lt_or_eq with
      hden | hden
    · rw [div_le_one hden]
      nlinarith [sq_nonneg ω, sq_nonneg (p.M * ω ^ 2), mul_nonneg (sq_nonneg ω)
        (mul_nonneg (sq_nonneg ω) (sq_nonneg p.M))]
    · rw [← hden, div_zero]; exact zero_le_one

/-- No amplification of grid-frequency oscillations: `|H(jω)| ≤ 1` at every frequency iff
`ζ² ≥ 1/2` (`M, K > 0`; equivalently `2MK ≤ D²`). Below that damping the converter frequency
amplifies a band of oscillations of the grid frequency. -/
@[tmio M, powerlib_domain] theorem normSq_transferFn_le_one_iff (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hK : 0 < p.syncCoeff δ) :
    (∀ ω : ℝ, normSq (transferFn p δ ((ω : ℂ) * I)) ≤ 1) ↔
      1 / 2 ≤ Criteria.dampingRatio (p.jacobian δ) ^ 2 := by
  rw [normSq_le_one_iff_aux p hM, p.dampingRatio_jacobian hM hK, div_pow, mul_pow,
    Real.sq_sqrt (by positivity), le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-! ## ROCOF: derivative output -/

/-- The converter ROCOF `d/dt Δω` read off the frequency channel (`LTI.derivModel`). -/
def rocofPlant (p : SwingParams) (δ : ℝ) : Linear.Plant 2 1 := LTI.derivModel (frequencyPlant p δ)

/-- `ROCOF(s)/Δω_g(s) = s H(s)` (`M ≠ 0`, `s` not a characteristic root). -/
@[tmio M, powerlib_domain] theorem transfer_rocofPlant (p : SwingParams) {δ : ℝ} (hM : p.M ≠ 0)
    {s : ℂ} (hs : (p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s + (p.syncCoeff δ : ℂ) ≠ 0) :
    Linear.transfer (rocofPlant p δ) s = !![s * transferFn p δ s] := by
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hdet : (Linear.characteristicMatrix (frequencyPlant p δ).A s).det ≠ 0 := by
    rw [show (frequencyPlant p δ).A = p.jacobian δ from rfl]
    intro h
    apply hs
    rw [← p.characteristic_polynomial hM δ s, h, mul_zero]
  rw [rocofPlant, LTI.transfer_derivModel rfl hdet, transfer_frequencyPlant p hM]
  ext i j; fin_cases i; fin_cases j; simp

/-- Noise amplification of differentiation: `|jω H(jω)|² = ω² |H(jω)|²`. -/
@[tmio M, powerlib_domain] theorem normSq_rocof (p : SwingParams) (δ ω : ℝ) :
    normSq (((ω : ℂ) * I) * transferFn p δ ((ω : ℂ) * I)) =
      ω ^ 2 * normSq (transferFn p δ ((ω : ℂ) * I)) := by
  rw [Complex.normSq_mul]
  congr 1
  simp [Complex.normSq_apply]; ring

/-- The ROCOF gain never exceeds `K/D`: `|jω H(jω)|² ≤ (K/D)²` at every frequency (`D ≠ 0`). -/
@[tmio M, powerlib_domain] theorem normSq_rocof_le (p : SwingParams) {δ : ℝ} (hD : p.D ≠ 0)
    (ω : ℝ) :
    normSq (((ω : ℂ) * I) * transferFn p δ ((ω : ℂ) * I)) ≤ (p.syncCoeff δ / p.D) ^ 2 := by
  rw [normSq_rocof, normSq_transferFn]
  set K := p.syncCoeff δ
  rcases (add_nonneg (sq_nonneg (K - p.M * ω ^ 2)) (sq_nonneg (p.D * ω))).lt_or_eq with
    hden | hden
  · rw [mul_div_assoc', div_pow, div_le_div_iff₀ hden (by positivity)]
    nlinarith [sq_nonneg (K * (K - p.M * ω ^ 2)), sq_nonneg (K - p.M * ω ^ 2)]
  · rw [← hden, div_zero, mul_zero]; positivity

/-- The bound is attained at the natural frequency: `|jω_n H(jω_n)|² = (K/D)²`
(`M, K > 0`, `D ≠ 0`). -/
@[tmio M, powerlib_domain] theorem normSq_rocof_naturalFrequency (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hK : 0 < p.syncCoeff δ) (hD : p.D ≠ 0) :
    normSq (((Criteria.naturalFrequency (p.jacobian δ) : ℂ) * I) *
        transferFn p δ ((Criteria.naturalFrequency (p.jacobian δ) : ℂ) * I)) =
      (p.syncCoeff δ / p.D) ^ 2 := by
  obtain ⟨hn, -⟩ := jacobian_data p hM hK
  rw [normSq_rocof, normSq_transferFn, hn, show p.syncCoeff δ - p.M * (p.syncCoeff δ / p.M) = 0
    by field_simp; ring]
  have hω : (p.D * Criteria.naturalFrequency (p.jacobian δ)) ^ 2 =
      p.D ^ 2 * (p.syncCoeff δ / p.M) := by rw [mul_pow, hn]
  rw [hω]
  field_simp
  ring

/-- The three-state converter ROCOF (`LTI.derivModel` of the three-state frequency channel). -/
def filterRocofPlant (g : VSMLPF) (δ : ℝ) : Linear.Plant 3 1 :=
  LTI.derivModel (filterFrequencyPlant g δ)

/-- Three states: `ROCOF(s)/Δω_g(s) = s H₃(s)` (`M ≠ 0`, `s` not a characteristic root). -/
@[tmio M, powerlib_domain] theorem transfer_filterRocofPlant (g : VSMLPF) {δ : ℝ}
    (hM : g.M ≠ 0) {s : ℂ}
    (hs : (Linear.characteristicMatrix (g.jacobian δ) s).det ≠ 0) :
    Linear.transfer (filterRocofPlant g δ) s = !![s * filterTransferFn g δ s] := by
  rw [filterRocofPlant, LTI.transfer_derivModel rfl hs, transfer_filterFrequencyPlant g hM]
  ext i j; fin_cases i; fin_cases j; simp

/-! ## The power filter and the double-frequency ripple -/

/-- The power filter `Ṗ_f = ω_c (P_e − P_f)`: state and output `P_f`, input `P_e`. -/
def powerFilterPlant (ωc : ℝ) : Linear.Plant 1 1 := ⟨!![-ωc], !![ωc], !![1], !![0]⟩

/-- `P_f(s)/P_e(s) = F(s) = ω_c/(s + ω_c)` (`s ≠ −ω_c`). -/
@[tmio M, powerlib_domain] theorem transfer_powerFilterPlant (ωc : ℝ) {s : ℂ}
    (hs : s + ωc ≠ 0) : Linear.transfer (powerFilterPlant ωc) s 0 0 = ωc / (s + ωc) := by
  rw [powerFilterPlant, LTI.transfer_fin_one _ _ _ _ (by simpa using hs)]
  push_cast
  ring

/-- Attenuation of a double-frequency ripple: `|F(2jω₀)|² = ω_c²/(ω_c² + 4ω₀²)` (`ω_c ≠ 0`). -/
@[tmio M, powerlib_domain] theorem normSq_powerFilter_ripple {ωc : ℝ} (hωc : ωc ≠ 0) (ω₀ : ℝ) :
    normSq (Linear.transfer (powerFilterPlant ωc) (2 * (ω₀ : ℂ) * I) 0 0) =
      ωc ^ 2 / (ωc ^ 2 + 4 * ω₀ ^ 2) := by
  have hs : 2 * (ω₀ : ℂ) * I + ωc = ⟨ωc, 2 * ω₀⟩ := by apply Complex.ext <;> simp
  have hne : 2 * (ω₀ : ℂ) * I + ωc ≠ 0 := by
    rw [hs]; intro h; have := congrArg Complex.re h; simp at this; exact hωc this
  rw [transfer_powerFilterPlant ωc hne, hs, Complex.normSq_div, Complex.normSq_ofReal,
    Complex.normSq_mk]
  ring

/-- The forced response of the filter to the ripple `P_e = R cos(2ω₀ t)`:
`R (ω_c² cos 2ω₀t + 2ω₀ω_c sin 2ω₀t)/(ω_c² + 4ω₀²)`. -/
def rippleResponse (ωc ω₀ R t : ℝ) : Fin 1 → ℝ :=
  ![R * (ωc ^ 2 * Real.cos (2 * ω₀ * t) + 2 * ω₀ * ωc * Real.sin (2 * ω₀ * t)) /
    (ωc ^ 2 + 4 * ω₀ ^ 2)]

/-- The forced response is a forward trajectory of the filter under the ripple input
(`ω_c ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem rippleResponse_isTrajectory {ωc : ℝ} (hωc : ωc ≠ 0)
    (ω₀ R : ℝ) :
    ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt (rippleResponse ωc ω₀ R)
      ((powerFilterPlant ωc).A *ᵥ rippleResponse ωc ω₀ R t +
        (powerFilterPlant ωc).B *ᵥ ![R * Real.cos (2 * ω₀ * t)]) (Set.Ici 0) t := by
  intro t _
  have hden : ωc ^ 2 + 4 * ω₀ ^ 2 ≠ 0 := by positivity
  apply HasDerivAt.hasDerivWithinAt
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  have hc := ((Real.hasDerivAt_cos (2 * ω₀ * t)).comp t
    (((hasDerivAt_id t).const_mul (2 * ω₀)))).const_mul (ωc ^ 2)
  have hs := ((Real.hasDerivAt_sin (2 * ω₀ * t)).comp t
    (((hasDerivAt_id t).const_mul (2 * ω₀)))).const_mul (2 * ω₀ * ωc)
  have h := ((hc.add hs).const_mul R).div_const (ωc ^ 2 + 4 * ω₀ ^ 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [powerFilterPlant, rippleResponse]
    field_simp
    ring
  · exact Filter.Eventually.of_forall fun τ => by simp [rippleResponse]

/-- The forced ripple is `R Re(F(2jω₀) e^{2jω₀t})`: amplitude `|F(2jω₀)| R`, phase `arg F`. -/
@[tmio M, powerlib_domain] theorem rippleResponse_eq {ωc : ℝ} (hωc : ωc ≠ 0) (ω₀ R t : ℝ) :
    rippleResponse ωc ω₀ R t 0 =
      R * (Linear.transfer (powerFilterPlant ωc) (2 * (ω₀ : ℂ) * I) 0 0 *
        Complex.exp ((2 * ω₀ * t : ℝ) * I)).re := by
  have hs : 2 * (ω₀ : ℂ) * I + ωc = ⟨ωc, 2 * ω₀⟩ := by apply Complex.ext <;> simp
  have hne : 2 * (ω₀ : ℂ) * I + ωc ≠ 0 := by
    rw [hs]; intro h; have := congrArg Complex.re h; simp at this; exact hωc this
  have hden : ωc ^ 2 + 4 * ω₀ ^ 2 ≠ 0 := by positivity
  rw [transfer_powerFilterPlant ωc hne, hs, Complex.exp_mul_I, Complex.mul_re, Complex.div_re,
    Complex.div_im, Complex.normSq_mk]
  simp only [rippleResponse, Matrix.cons_val_zero, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp
  ring

end powerlib.GFM.Tracking
