import theorem.GridTiedConverter.GFM.HopfLyapunovCurrent
import theorem.GridTiedConverter.GFM.Line.VSMLPF

/-! # The `ε = 1/ω_b` law of the Hopf points of the VSM on a dynamic R–L line

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle, the field translated so that the
  operating point is the origin.
* The fast-line family `Line.VSM.Model.atScale m ε D`
  (`theorem/GridTiedConverter/GFM/Line/VSMLPF.lean`): `E`, `V`, `R`, the reactance `X` (hence the
  power curve, `P(δ*)`, `K = P'(δ*)`, `Q = Q(δ*)`, `c₀ = E²R/|Z|²`), `M`, `P_ref` and the angle
  `δ*` of a model `m` are fixed, the line has time scale `ε = 1/ω_b` (`ω₀ = 1/ε`, `L = εX`) and the
  damping `D > 0` is free; `ε → 0⁺` only. `m` is physical with `R > 0` and `K > 0` (so
  `a₀ = ρK/M > 0`); the first-Lyapunov and connection conclusions also need `m` balanced
  (`P(δ*) = P_ref`, then `P''(δ*) = c₀ − P_ref`).
* The Hopf boundary: the third Hurwitz determinant of the monic quartic at the operating point
  vanishes, `a₃a₂a₁ = a₁² + a₃²a₀` (`Line.VSM.coeff3` … `coeff0`).
* Level: exact signs for all parameters of the stated region and every `ε` below an `ε₀ > 0`
  depending on the model, the location of the boundary dampings, and Lyapunov instability / local
  asymptotic stability (LeanForControl's `Unstable`, `LocalAsymptoticStable`) through the family
  laws; the limit of `ℓ₁/(|q₀|² ε³)` (`|q₀|²` normalises the critical vector to angle component
  `1`) uniformly over the boundary dampings and critical pairs. Not stated: the next order of
  `ℓ₁` (in the degenerate cases `R = X` and `5K² = P''²` the leading term vanishes and the sign
  is not decided here), the uniqueness and orbital stability of the
  bifurcating cycles. Their existence at every boundary point with `ℓ₁ ≠ 0` (hence on fast
  lines wherever `(X² − R²)(5K² − P''²) ≠ 0`), along the damping or, where it is not transversal,
  along the inverse inertia, is `theorem/GridTiedConverter/GFM/LineVSMHopfCycle.lean` (private
  evidence `Line.VSM.Model.exists_hopfCycle_of_bautinFormAngle_ne`).

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c) and its script
`s5f_slow_manifold.py` (`D_H = ε 2E²RX²/|Z|⁴ + O(ε²)`, `ℓ₁ = ε³ L₃ + O(ε⁴)`,
`L₃ = E²RX⁴(X² − R²)(5K² − P''²)/(K^{3/2} M^{3/2} |Z|⁸)`, from a formal `ε`-expansion of a truncated
Liénard–Rayleigh reduction; discovery evidence only). Here the law is derived from the exact
closed form of `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean`
(`Line.VSM.Model.sign_firstLyapunov_crit`: `sign ℓ₁ = −sign 𝔅_δ`): the weighted homogeneity of
`𝔅_δ` and its limit value were found with SymPy in exact arithmetic (untrusted) and are proved
here by `ring`; the boundary dampings are localized by `Line.VSM.Model.exists_routh_sandwich`
(`theorem/GridTiedConverter/GFM/Line/VSMLPF.lean`); Kuznetsov, *Elements of Applied Bifurcation
Theory* (3rd ed.), §3.5.

Results.
* Weighted homogeneity (`d, σ, ω₀` weight 1, `κ` weight 2, `t` weight 3):
  `Line.VSM.bautinFormQ_scale`, `Line.VSM.bautinCorr_scale` (degree 11),
  `Line.VSM.bautinFormAngle_scale` (degree 20).
* The scaled form: `Line.VSM.scaleBracket`, `Line.VSM.bautinFormAngle_eq_scaleBracket`
  (`𝔅_δ(zy, r, 1, zκ, zτ) = z² 𝔅̂(z, y)`), `Line.VSM.bautinFormQ_zero_one`
  (`𝔅_Q(0, r, 1, 0) = −2r³(r² − 1)(r² + 1)²(r² − 5)`), `Line.VSM.bautinCorr_zero_one`
  (`𝔊(0, r, 1, 0) = 8r³(r² − 1)(r² + 1)³`), `Line.VSM.scaleBracket_zero`
  (`𝔅̂(0, 2r(k + κ)/(1 + r²)) = −64r⁶(r² − 1)(1 + r²)³((kr − τ)² − 5k²)`),
  `Line.VSM.continuous_scaleBracket`. On the fast line `r = R/X`, `κ = Q/M`, `k = K/M`,
  `τ = (P_ref − rQ)/M`, `z = ε²`, `y = D/(εM)`, and `kr − τ = (c₀ − P_ref)/M`.
* **The boundary dampings** (`Line.VSM.Model.exists_atScale_hopf`): there are `C, ε₀ > 0` such
  that for every `ε ∈ (0, ε₀)` the Hopf boundary has a damping `D > 0`, and every boundary
  damping has `a₁ > 0` (a pair `±iω`, `ω² = a₁/a₃`, and a stable pair) and
  `D_line(ε)(1 − Cε²) < D < D_line(ε)(1 + Cε²)`, `D_line(ε) = ε · 2E²RX²/|Z|⁴`
  (`Line.VSM.Model.DlineAt`): the study's `D_H = ε 2E²RX²/|Z|⁴ + O(ε²)` with relative error
  `O(ε²)`.
* **The leading coefficient** (`Line.VSM.Model.exists_atScale_firstLyapunov_div_cube`): for a
  balanced physical model with `R, K > 0`, `ℓ₁/(|q₀|² ε³) → L₃ =
  E² R X⁴ (X² − R²)(5K² − P''²)/(K^{3/2} M^{3/2} |Z|⁸)` as `ε → 0⁺`, uniformly over the Hopf
  boundary dampings and their critical pairs — the study's `ℓ₁ = ε³ L₃ + o(ε³)` with the critical
  vector normalised to angle component `1` (through `Line.VSM.scaleL1`, its value
  `−r(k + κ)(r² − 1)(5k² − (kr − τ)²)/(√k k (1 + r²)³)` at `ε = 0` and its continuity;
  the ratio `ℓ₁/|q₀|²` is the same for every critical pair, `firstLyapunov_smul`).
* **The sign law** (`Line.VSM.Model.exists_atScale_sign_bautinFormAngle`,
  `Line.VSM.Model.exists_atScale_sign_firstLyapunov`): if `(X² − R²)(5K² − (c₀ − P_ref)²) ≠ 0`,
  then for every `ε ∈ (0, ε₀)`, every boundary damping and every critical pair,
  `sign ℓ₁ = sign((X² − R²)(5K² − P''²))` — the sign of the study's `L₃`; subcritical iff
  `(X − R)(5K² − P''²) > 0`. On the zero-current slice (`V = E`, `δ* = 0`: `K = E²X/|Z|²`,
  `P'' = E²R/|Z|²`) the factor is `(X² − R²)(5X² − R²)`.

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.Model.atScale_mem_den_unstable`: a balanced physical model with `R, K > 0` and
  `(X² − R²)(5K² − P''²) > 0` has `ε₀ > 0` such that on every line of time scale `ε < ε₀` the
  Hopf boundary contains an unstable model and every boundary model is unstable (subcritical
  Hopf points; `Line.VSM.mem_den_unstable_of_bautinFormAngle_neg`).
* `Line.VSM.Model.atScale_mem_den_locallyAsymptoticallyStable`: with
  `(X² − R²)(5K² − P''²) < 0` instead, every boundary model is locally asymptotically stable
  (supercritical; `Line.VSM.mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos`).
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Filter Topology
open powerlib.NormalForm.LyapunovCoefficient

/-- **Weighted homogeneity of `𝔅_Q`** (`d, σ, ω₀` weight 1, `κ` weight 2, degree 11). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinFormQ_scale (c d σ w κ : ℝ) :
    bautinFormQ (c * d) (c * σ) (c * w) (c ^ 2 * κ) = c ^ 11 * bautinFormQ d σ w κ := by
  unfold bautinFormQ; ring

/-- **Weighted homogeneity of `𝔊`** (degree 11). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinCorr_scale (c d σ w κ : ℝ) :
    bautinCorr (c * d) (c * σ) (c * w) (c ^ 2 * κ) = c ^ 11 * bautinCorr d σ w κ := by
  unfold bautinCorr; ring

/-- **Weighted homogeneity of `𝔅_δ`** (`t` weight 3, degree 20). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinFormAngle_scale (c d σ w κ t : ℝ) :
    bautinFormAngle (c * d) (c * σ) (c * w) (c ^ 2 * κ) (c ^ 3 * t) =
      c ^ 20 * bautinFormAngle d σ w κ t := by
  unfold bautinFormAngle
  rw [bautinFormQ_scale, bautinCorr_scale]
  ring

/-- The bracket `𝔅̂(z, y)` of the scaled Bautin form `𝔅_δ(zy, r, 1, zκ, zτ) = z² 𝔅̂(z, y)`
(`bautinFormAngle_eq_scaleBracket`), a polynomial in `z`, `y` and the parameters `r, κ, τ`. -/
def scaleBracket (r κ τ z y : ℝ) : ℝ :=
  4 * (y * (1 + r ^ 2) - 2 * r * κ) ^ 2 *
      (2 * r * (1 + r ^ 2) + 4 * r ^ 2 * (z * y) + 2 * r * (z * y) ^ 2 - z * y * (z * κ)) *
      bautinFormQ (z * y) r 1 (z * κ) +
    τ * (2 * (z * y + 2 * r) ^ 2 * (z * y + r) * (y * (1 + r ^ 2) - 2 * r * κ) -
      (z * y + 2 * r) ^ 3 * τ) * bautinCorr (z * y) r 1 (z * κ)

/-- **The scaled Bautin form**: `𝔅_δ(zy, r, 1, zκ, zτ) = z² 𝔅̂(z, y)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bautinFormAngle_eq_scaleBracket (r κ τ z y : ℝ) :
    bautinFormAngle (z * y) r 1 (z * κ) (z * τ) = z ^ 2 * scaleBracket r κ τ z y := by
  unfold bautinFormAngle scaleBracket; ring

/-- `𝔅_Q(0, r, 1, 0) = −2r³(r² − 1)(r² + 1)²(r² − 5)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinFormQ_zero_one (r : ℝ) :
    bautinFormQ 0 r 1 0 = -(2 * r ^ 3 * (r ^ 2 - 1) * (r ^ 2 + 1) ^ 2 * (r ^ 2 - 5)) := by
  unfold bautinFormQ; ring

/-- `𝔊(0, r, 1, 0) = 8r³(r² − 1)(r² + 1)³`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinCorr_zero_one (r : ℝ) :
    bautinCorr 0 r 1 0 = 8 * r ^ 3 * (r ^ 2 - 1) * (r ^ 2 + 1) ^ 3 := by
  unfold bautinCorr; ring

/-- **The limit value of the bracket**: at `z = 0`, `y = 2r(k + κ)/(1 + r²)`,
`𝔅̂ = −64r⁶(r² − 1)(1 + r²)³((kr − τ)² − 5k²)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem scaleBracket_zero (r κ k τ : ℝ) :
    scaleBracket r κ τ 0 (2 * r * (k + κ) / (1 + r ^ 2)) =
      -(64 * r ^ 6 * (r ^ 2 - 1) * (1 + r ^ 2) ^ 3 * ((k * r - τ) ^ 2 - 5 * k ^ 2)) := by
  have h1 : (1 + r ^ 2) ≠ 0 := by positivity
  unfold scaleBracket
  simp only [zero_mul, bautinFormQ_zero_one, bautinCorr_zero_one]
  field_simp
  ring

/-- The bracket is continuous (a polynomial). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem continuous_scaleBracket (r κ τ : ℝ) :
    Continuous (fun p : ℝ × ℝ => scaleBracket r κ τ p.1 p.2) := by
  unfold scaleBracket bautinFormQ bautinCorr
  fun_prop

/-! ## The scaled models -/

section
variable (m : Model) {ε : ℝ} (D : ℝ)

@[tmio M, powerlib_domain] private theorem sc_X (hε : ε ≠ 0) : (m.atScale ε D).g.X = m.g.X := by
  simp only [Model.atScale, Network.X]
  field_simp

@[tmio M, powerlib_domain] private theorem sc_absSq (hε : ε ≠ 0) :
    (m.atScale ε D).g.absSq = m.g.absSq := by
  rw [Network.absSq, sc_X m D hε]; rfl

@[tmio M, powerlib_domain] private theorem sc_Q (hε : ε ≠ 0) (hZ : m.g.absSq ≠ 0) :
    (m.atScale ε D).Q = m.Q := by
  have hZ' : (m.atScale ε D).g.absSq ≠ 0 := by rwa [sc_absSq m D hε]
  rw [Model.Q, Model.Q, Network.qssReactive_eq _ hZ', Network.qssReactive_eq _ hZ, sc_X m D hε,
    sc_absSq m D hε]
  rfl

@[tmio M, powerlib_domain] private theorem sc_K (hε : ε ≠ 0) : (m.atScale ε D).K = m.K := by
  simp only [Model.K, Network.syncCoeff, Network.A, Network.α, sc_absSq m D hε, sc_X m D hε]
  rfl

@[tmio M, powerlib_domain] private theorem sc_qssPower (hε : ε ≠ 0) (hZ : m.g.absSq ≠ 0) :
    (m.atScale ε D).g.qssPower (m.atScale ε D).δ = m.g.qssPower m.δ := by
  have hZ' : (m.atScale ε D).g.absSq ≠ 0 := by rwa [sc_absSq m D hε]
  rw [Network.qssPower_eq _ hZ', Network.qssPower_eq _ hZ, sc_X m D hε, sc_absSq m D hε]
  rfl

@[tmio M, powerlib_domain] private theorem sc_physical (hp : Meets m .physical) (hε : 0 < ε)
    (hD : 0 < D) : Meets (m.atScale ε D) .physical :=
  ⟨⟨hp.1.E, hp.1.V, hp.1.R, mul_pos hε hp.1.X_pos, one_div_pos.mpr hε⟩, hp.2.1, hD⟩

/-- The monic coefficients of the scaled model in `r = R/X`, `q = Q/M`, `k = K/M`. -/
@[tmio M, powerlib_domain] private theorem sc_coeffs (hp : Meets m .physical) (hε : 0 < ε) :
    (m.atScale ε D).g.coeff3 = 2 * (m.g.R / m.g.X) / ε + D / m.g.M ∧
      (m.atScale ε D).g.coeff2 (m.atScale ε D).Q =
        (1 + (m.g.R / m.g.X) ^ 2) / ε ^ 2 + 2 * (m.g.R / m.g.X) / ε * (D / m.g.M) -
          m.Q / m.g.M ∧
      (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        D / m.g.M * ((1 + (m.g.R / m.g.X) ^ 2) / ε ^ 2) -
          2 * (m.g.R / m.g.X) / ε * (m.Q / m.g.M) ∧
      (m.atScale ε D).g.coeff0 (m.atScale ε D).Q =
        (1 + (m.g.R / m.g.X) ^ 2) / ε ^ 2 * (m.K / m.g.M) := by
  have hX := hp.1.X_pos
  have hZ := hp.1.absSq_pos
  have hM := hp.2.1
  have hL : (m.atScale ε D).g.L ≠ 0 := mul_ne_zero hε.ne' hX.ne'
  have hZ' : 0 < (m.atScale ε D).g.absSq := by rwa [sc_absSq m D hε.ne']
  have hQ := sc_Q m D hε.ne' hZ.ne'
  have hσ : (m.atScale ε D).g.σ = m.g.R / m.g.X / ε := by
    simp only [Network.σ, Model.atScale]; ring
  have hρ : (m.atScale ε D).g.ρ = (1 + (m.g.R / m.g.X) ^ 2) / ε ^ 2 := by
    rw [Network.ρ, hσ, sc_X m D hε.ne']
    simp only [Model.atScale]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff3, hσ]; simp only [Model.atScale]; ring
  · rw [coeff2, hσ, hρ, hQ]; simp only [Model.atScale]; ring
  · rw [coeff1, hσ, hρ, hQ]; simp only [Model.atScale]; ring
  · rw [Model.coeff0_eq _ hL hZ', hρ, sc_K m D hε.ne']; simp only [Model.atScale]; ring

end
/-- **The Hopf dampings of a fast line**: for a physical model with `R, K > 0` there are
`C, ε₀ > 0` such that on every line of time scale `ε ∈ (0, ε₀)` some damping `D > 0` puts the
model on the Hopf boundary, and every such damping has `a₁ > 0` and lies in
`(D_line(ε)(1 − Cε²), D_line(ε)(1 + Cε²))`, `D_line(ε) = ε · 2E²RX²/|Z|⁴`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.exists_atScale_hopf (m : Model)
    (hp : Meets m .physical) (hR : 0 < m.g.R) (hK : 0 < m.K) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      (∃ D : ℝ, 0 < D ∧
        (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
            (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
            (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q) ∧
      ∀ D : ℝ, 0 < D →
        (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
            (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
            (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
        0 < (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ∧
          m.DlineAt ε * (1 - C * ε ^ 2) < D ∧ D < m.DlineAt ε * (1 + C * ε ^ 2) := by
  have hX := hp.1.X_pos
  have hZ := hp.1.absSq_pos
  have hM := hp.2.1
  have hE := hp.1.E
  obtain ⟨C, hC, ε1, hε1, H⟩ := m.exists_routh_sandwich hE.ne' hR hX hM hK
  set r := m.g.R / m.g.X with hr
  set q := m.Q / m.g.M with hq
  set k := m.K / m.g.M with hk
  have hr0 : 0 < r := div_pos hR hX
  have hk0 : 0 < k := div_pos hK hM
  have hqk : 0 < q + k := by
    have h := m.g.syncCoeff_add_qssReactive hZ m.δ
    have hκ : 0 < m.g.κ := by unfold Network.κ; positivity
    rw [hq, hk, ← add_div]
    apply div_pos _ hM
    rw [Model.Q, Model.K]; linarith
  refine ⟨C, hC, min ε1 (min 1 (1 / (1 + |q|))), by positivity, fun ε hε hεε0 => ?_⟩
  have hεε1 : ε < ε1 := lt_of_lt_of_le hεε0 (min_le_left _ _)
  have hε1' : ε < 1 := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_left _ _))
  have hεq : ε < 1 / (1 + |q|) := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_right _ _))
  have hεq' : ε ^ 2 * q < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hεq
    have : ε ^ 2 * q ≤ ε * |q| := by
      have h1 : ε ^ 2 * q ≤ ε ^ 2 * |q| := mul_le_mul_of_nonneg_left (le_abs_self q) (by positivity)
      have h2 : ε ^ 2 * |q| ≤ ε * |q| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg q); nlinarith
      linarith
    nlinarith
  -- the coefficients as functions of the damping
  have e := fun D => sc_coeffs m D hp hε
  have ha2 : ∀ D : ℝ, 0 < D → 0 < (m.atScale ε D).g.coeff2 (m.atScale ε D).Q := by
    intro D hD
    rw [(e D).2.1]
    have h1 : 0 < (1 + r ^ 2) / ε ^ 2 - q := by
      rw [div_sub' (by positivity), lt_div_iff₀ (by positivity)]; nlinarith
    have h2 : 0 < 2 * r / ε * (D / m.g.M) := by positivity
    linarith
  have ha3 : ∀ D : ℝ, 0 < D → 0 < (m.atScale ε D).g.coeff3 := by
    intro D hD; rw [(e D).1]; positivity
  have ha0 : ∀ D : ℝ, 0 < (m.atScale ε D).g.coeff0 (m.atScale ε D).Q := by
    intro D; rw [(e D).2.2.2]; positivity
  have hpos : ∀ D : ℝ, 0 < D →
      (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
      0 < (m.atScale ε D).g.coeff1 (m.atScale ε D).Q := by
    intro D hD hH
    have h3 := ha3 D hD
    have h2 := ha2 D hD
    have h0 := ha0 D
    set a3 := (m.atScale ε D).g.coeff3
    set a2 := (m.atScale ε D).g.coeff2 (m.atScale ε D).Q
    set a1 := (m.atScale ε D).g.coeff1 (m.atScale ε D).Q
    set a0 := (m.atScale ε D).g.coeff0 (m.atScale ε D).Q
    have hprod : 0 < a1 * (a3 * a2 - a1) := by nlinarith [mul_pos (pow_pos h3 2) h0]
    by_contra hn
    push Not at hn
    have : 0 < a3 * a2 - a1 := by nlinarith [mul_pos h3 h2]
    nlinarith
  refine ⟨?_, fun D hD hH => ⟨hpos D hD hH, ?_, ?_⟩⟩
  · -- existence: the third Hurwitz determinant changes sign on `[0, D_line(1 + Cε²)]`
    set f : ℝ → ℝ := fun D =>
      (2 * r / ε + D / m.g.M) * ((1 + r ^ 2) / ε ^ 2 + 2 * r / ε * (D / m.g.M) - q) *
          (D / m.g.M * ((1 + r ^ 2) / ε ^ 2) - 2 * r / ε * q) -
        (D / m.g.M * ((1 + r ^ 2) / ε ^ 2) - 2 * r / ε * q) ^ 2 -
        (2 * r / ε + D / m.g.M) ^ 2 * ((1 + r ^ 2) / ε ^ 2 * k) with hf
    have hfD : ∀ D, f D = (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q -
        ((m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q) := by
      intro D
      rw [(e D).1, (e D).2.1, (e D).2.2.1, (e D).2.2.2, hf]
      simp only [hr, hq, hk]
      ring
    have hf0 : f 0 < 0 := by
      have : f 0 = -(4 * r ^ 2 * (1 + r ^ 2) * (q + k) / ε ^ 4) := by
        rw [hf]; field_simp; ring
      rw [this]; linarith [show 0 < 4 * r ^ 2 * (1 + r ^ 2) * (q + k) / ε ^ 4 by positivity]
    set Dp := m.DlineAt ε * (1 + C * ε ^ 2) with hDp
    have hDl : 0 < m.DlineAt ε := by unfold Model.DlineAt; positivity
    have hDp0 : 0 < Dp := by positivity
    have hfp : 0 < f Dp := by
      obtain ⟨-, -, -, hg⟩ := (H ε hε hεε1 Dp hDp0).1 le_rfl
      rw [hfD]; linarith
    have hcont : ContinuousOn f (Set.Icc 0 Dp) := by
      apply Continuous.continuousOn; rw [hf]; fun_prop
    obtain ⟨D, ⟨hD0, -⟩, hfD0⟩ :=
      intermediate_value_Icc hDp0.le hcont ⟨hf0.le, hfp.le⟩
    have hDpos : 0 < D := by
      rcases hD0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hfD0; linarith
    exact ⟨D, hDpos, by have := hfD D; linarith⟩
  · by_contra hn
    push Not at hn
    have hv := (H ε hε hεε1 D hD).2 hn
    have h1 := hpos D hD hH
    have h3 := ha3 D hD
    have h2 := ha2 D hD
    have h0 := ha0 D
    rcases hv with v | v | v | v | v <;> linarith
  · by_contra hn
    push Not at hn
    obtain ⟨-, -, -, hg⟩ := (H ε hε hεε1 D hD).1 hn
    linarith

/-- The angle term of the scaled model. -/
@[tmio M, powerlib_domain] private theorem sc_angleShift (m : Model) {ε : ℝ} (D : ℝ)
    (hp : Meets m .physical) (hε : 0 < ε) :
    (m.atScale ε D).angleShift =
      (1 / ε) ^ 3 * (ε ^ 2 * ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M)) := by
  have hX := hp.1.X_pos
  have hM := hp.2.1
  rw [Model.angleShift, sc_Q m D hε.ne' hp.1.absSq_pos.ne']
  simp only [Model.atScale]
  field_simp

@[tmio T, powerlib_foundation] private theorem alg_dl {ε A Z M : ℝ} (hM : M ≠ 0) :
    ε * (A / Z) = ε * M * (A / (Z * M)) := by
  field_simp

@[tmio T, powerlib_foundation] private theorem alg_dy {D ε M y yh : ℝ} (hε : ε ≠ 0) (hM : M ≠ 0)
    (hy : y = D / (ε * M)) : y - yh = (D - ε * M * yh) / (ε * M) := by
  rw [hy]; field_simp

@[tmio T, powerlib_foundation] private theorem alg_a1 {D ε M y : ℝ} (hε : ε ≠ 0) (hM : M ≠ 0)
    (hy : y = D / (ε * M)) : 1 / ε * (ε ^ 2 * y) = D / M := by
  rw [hy]; field_simp

@[tmio T, powerlib_foundation] private theorem alg_a2 {ε R X : ℝ} (hε : ε ≠ 0) (hX : X ≠ 0) :
    1 / ε * (R / X) = R / (ε * X) := by
  field_simp

@[tmio T, powerlib_foundation] private theorem alg_a4 {ε Q M : ℝ} (hε : ε ≠ 0) :
    (1 / ε) ^ 2 * (ε ^ 2 * (Q / M)) = Q / M := by
  field_simp

/-- Near `(0, ŷ)` the bracket has the sign of its value there. -/
@[tmio M, powerlib_domain] private theorem exists_sign_scaleBracket (r q τ yh : ℝ)
    (h : scaleBracket r q τ 0 yh ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ z y : ℝ, |z| < η → |y - yh| < η →
      SignType.sign (scaleBracket r q τ z y) = SignType.sign (scaleBracket r q τ 0 yh) := by
  set c2 := scaleBracket r q τ 0 yh with hc2
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_scaleBracket r q τ).continuousAt |c2| (abs_pos.mpr h)
  refine ⟨η, hη, fun z y hz hy => ?_⟩
  have hd : dist (z, y) ((0 : ℝ), yh) < η := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]; exact max_lt hz hy
  have h' := hcont hd
  rw [Real.dist_eq] at h'
  simp only at h'
  rcases lt_or_gt_of_ne h with hn | hn
  · rw [abs_of_neg hn] at h'
    have : scaleBracket r q τ z y < 0 := by
      have := (abs_lt.mp h').2; linarith
    rw [sign_neg this, sign_neg hn]
  · rw [abs_of_pos hn] at h'
    have : 0 < scaleBracket r q τ z y := by
      have := (abs_lt.mp h').1; linarith
    rw [sign_pos this, sign_pos hn]

/-- The scaled damping and time scale are close to `(ŷ, 0)`. -/
@[tmio T, powerlib_foundation] private theorem scaled_close {ε η C yh M D : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hC : 0 < C) (hyh : 0 < yh) (hM : 0 < M)
    (hεη : ε < η / (1 + yh * C)) (hlo : ε * M * yh * (1 - C * ε ^ 2) < D)
    (hhi : D < ε * M * yh * (1 + C * ε ^ 2)) :
    |ε ^ 2| < η ∧ |D / (ε * M) - yh| < η := by
  have hb : 0 < 1 + yh * C := by positivity
  have hε2 : ε ^ 2 < ε := by nlinarith
  have hεη' : ε * (1 + yh * C) < η := by rwa [lt_div_iff₀ hb] at hεη
  have heM : 0 < ε * M := mul_pos hε hM
  constructor
  · rw [abs_of_pos (by positivity)]; nlinarith [mul_pos hyh hC]
  · have e : D / (ε * M) - yh = (D - ε * M * yh) / (ε * M) := by field_simp
    rw [e, abs_div, abs_of_pos heM, div_lt_iff₀ heM, abs_lt]
    have h1 : yh * C * ε ^ 2 ≤ yh * C * ε := by
      apply mul_le_mul_of_nonneg_left hε2.le; positivity
    have h2 : yh * C * ε < η := by nlinarith
    constructor <;> nlinarith [mul_pos heM (mul_pos hyh hC)]

/-- The Bautin form of the scaled model as `ε⁻¹⁶` times the bracket. -/
@[tmio M, powerlib_domain] private theorem sc_bautinFormAngle (m : Model) {ε : ℝ} (D : ℝ)
    (hp : Meets m .physical) (hε : 0 < ε) :
    bautinFormAngle ((m.atScale ε D).g.D / (m.atScale ε D).g.M)
        ((m.atScale ε D).g.R / (m.atScale ε D).g.L) (m.atScale ε D).g.ω0
        ((m.atScale ε D).Q / (m.atScale ε D).g.M) (m.atScale ε D).angleShift =
      (1 / ε) ^ 20 * ((ε ^ 2) ^ 2 * scaleBracket (m.g.R / m.g.X) (m.Q / m.g.M)
        ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M) (ε ^ 2) (D / (ε * m.g.M))) := by
  have hX := hp.1.X_pos
  have hM := hp.2.1
  have key := bautinFormAngle_scale (1 / ε) (ε ^ 2 * (D / (ε * m.g.M))) (m.g.R / m.g.X) 1
    (ε ^ 2 * (m.Q / m.g.M)) (ε ^ 2 * ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M))
  rw [bautinFormAngle_eq_scaleBracket] at key
  have a1 : 1 / ε * (ε ^ 2 * (D / (ε * m.g.M))) = (m.atScale ε D).g.D / (m.atScale ε D).g.M :=
    alg_a1 hε.ne' hM.ne' rfl
  have a2 : 1 / ε * (m.g.R / m.g.X) = (m.atScale ε D).g.R / (m.atScale ε D).g.L :=
    alg_a2 hε.ne' hX.ne'
  have a3 : 1 / ε * 1 = (m.atScale ε D).g.ω0 := by rw [mul_one]; rfl
  have a4 : (1 / ε) ^ 2 * (ε ^ 2 * (m.Q / m.g.M)) = (m.atScale ε D).Q / (m.atScale ε D).g.M := by
    rw [sc_Q m D hε.ne' hp.1.absSq_pos.ne']; exact alg_a4 hε.ne'
  rw [a1, a2, a3, a4, ← sc_angleShift m D hp hε] at key
  exact key

/-- The limit value of the bracket: `−(64 r⁶ (1 + r²)³/(X² M²)) (X² − R²)(5K² − (c₀ − P_ref)²)`. -/
@[tmio M, powerlib_domain] private theorem scaleBracket_limit (m : Model)
    (hp : Meets m .physical) :
    scaleBracket (m.g.R / m.g.X) (m.Q / m.g.M) ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M) 0
        (2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M)) =
      -(64 * (m.g.R / m.g.X) ^ 6 * (1 + (m.g.R / m.g.X) ^ 2) ^ 3 / (m.g.X ^ 2 * m.g.M ^ 2)) *
        ((m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2)) := by
  have hX := hp.1.X_pos
  have hZ := hp.1.absSq_pos
  have hM := hp.2.1
  have hQK : m.Q + m.K = m.g.E ^ 2 * m.g.X / m.g.absSq := by
    have h := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [Model.Q, Model.K, Network.κ] at *; linarith
  have hy : 2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M) =
      2 * (m.g.R / m.g.X) * (m.K / m.g.M + m.Q / m.g.M) / (1 + (m.g.R / m.g.X) ^ 2) := by
    rw [← add_div, add_comm m.K, hQK]
    unfold Network.absSq at hZ ⊢
    field_simp
    ring
  have hc0 : m.g.c0 = m.g.R / m.g.X * (m.Q + m.K) := by
    rw [hQK, Network.c0]; unfold Network.absSq at hZ ⊢; field_simp
  rw [hy, scaleBracket_zero, hc0]
  field_simp
  ring

/-- **The sign of the Bautin form on a fast line**: if `(X² − R²)(5K² − (c₀ − P_ref)²) ≠ 0`, then
below some `ε₀ > 0` every boundary damping has `sign 𝔅_δ = −sign((X² − R²)(5K² − (c₀ − P_ref)²))`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_atScale_sign_bautinFormAngle (m : Model)
    (hp : Meets m .physical) (hR : 0 < m.g.R) (hK : 0 < m.K)
    (hc : (m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2) ≠ 0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ D : ℝ, 0 < D →
      (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
      SignType.sign (bautinFormAngle ((m.atScale ε D).g.D / (m.atScale ε D).g.M)
          ((m.atScale ε D).g.R / (m.atScale ε D).g.L) (m.atScale ε D).g.ω0
          ((m.atScale ε D).Q / (m.atScale ε D).g.M) (m.atScale ε D).angleShift) =
        -SignType.sign ((m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2)) := by
  have hX := hp.1.X_pos
  have hM := hp.2.1
  obtain ⟨C, hC, ε1, hε1, H⟩ := m.exists_atScale_hopf hp hR hK
  have hfac : 0 < 64 * (m.g.R / m.g.X) ^ 6 * (1 + (m.g.R / m.g.X) ^ 2) ^ 3 /
      (m.g.X ^ 2 * m.g.M ^ 2) := by
    have : 0 < m.g.R / m.g.X := div_pos hR hX
    positivity
  have hlim := scaleBracket_limit m hp
  have hc2 : scaleBracket (m.g.R / m.g.X) (m.Q / m.g.M)
      ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M) 0
      (2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M)) ≠ 0 := by
    rw [hlim]; exact mul_ne_zero (neg_ne_zero.mpr hfac.ne') hc
  obtain ⟨η, hη, hsign⟩ := exists_sign_scaleBracket _ _ _ _ hc2
  have hyh : 0 < 2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M) := by
    have := hp.1.E; have := hp.1.absSq_pos; positivity
  refine ⟨min ε1 (min 1 (η / (1 + 2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 /
    (m.g.absSq ^ 2 * m.g.M) * C))), by positivity, fun ε hε hεε0 D hD hH => ?_⟩
  have hεε1 : ε < ε1 := lt_of_lt_of_le hεε0 (min_le_left _ _)
  have hε1' : ε < 1 := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_left _ _))
  have hεη := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, hlo, hhi⟩ := (H ε hε hεε1).2 D hD hH
  have hDl : m.DlineAt ε =
      ε * m.g.M * (2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M)) := by
    rw [Model.DlineAt]; exact alg_dl hM.ne'
  rw [hDl] at hlo hhi
  obtain ⟨hz, hy⟩ := scaled_close hε hε1' hC hyh hM hεη hlo hhi
  have hsc2 : SignType.sign (scaleBracket (m.g.R / m.g.X) (m.Q / m.g.M)
      ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M) 0
      (2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M))) =
      -SignType.sign ((m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2)) := by
    rw [hlim, neg_mul, Left.sign_neg, sign_mul _ ((m.g.X ^ 2 - m.g.R ^ 2) * _), sign_pos hfac,
      one_mul]
  rw [sc_bautinFormAngle m D hp hε, sign_mul, sign_pos (by positivity), one_mul, sign_mul,
    sign_pos (by positivity), one_mul, hsign _ _ hz hy, hsc2]

@[tmio M, powerlib_domain] private theorem sc_balanced (m : Model) {ε : ℝ} (D : ℝ)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hε : 0 < ε) :
    Meets (m.atScale ε D) .balanced := by
  change (m.atScale ε D).g.qssPower (m.atScale ε D).δ = m.g.Pref
  rw [sc_qssPower m D hε.ne' hp.1.absSq_pos.ne']; exact hb

@[tmio M, powerlib_domain] private theorem sc_coeff0_pos (m : Model) {ε : ℝ} (D : ℝ)
    (hp : Meets m .physical) (hK : 0 < m.K) (hε : 0 < ε) :
    0 < (m.atScale ε D).g.coeff0 (m.atScale ε D).Q := by
  have hM := hp.2.1
  rw [(sc_coeffs m D hp hε).2.2.2]; positivity

/-- **The `ε = 1/ω_b` law of the first Lyapunov coefficient**: for a balanced physical model with
`R, K > 0` and `(X² − R²)(5K² − P''²) ≠ 0` (`P'' = c₀ − P_ref`), below some `ε₀ > 0` every
critical pair of every Hopf boundary model of the fast line has
`sign ℓ₁ = sign((X² − R²)(5K² − P''²))`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_atScale_sign_firstLyapunov (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) (hK : 0 < m.K)
    (hc : (m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2) ≠ 0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ D : ℝ, 0 < D →
      (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
      ∀ (ω : ℝ) (q p : Fin 4 → ℂ), IsCriticalPair (m.atScale ε D).field 0 ω q p →
        SignType.sign (firstLyapunov (m.atScale ε D).field 0 ω q p) =
          SignType.sign ((m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2)) := by
  obtain ⟨C, -, ε1, hε1, H⟩ := m.exists_atScale_hopf hp hR hK
  obtain ⟨ε2, hε2, H2⟩ := m.exists_atScale_sign_bautinFormAngle hp hR hK hc
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun ε hε hεε0 D hD hH ω q p hcp => ?_⟩
  have h1 := ((H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _))).2 D hD hH).1
  have hs := H2 ε hε (lt_of_lt_of_le hεε0 (min_le_right _ _)) D hD hH
  rw [Model.sign_firstLyapunov_crit (sc_physical m D hp hε hD) (sc_balanced m D hp hb hε) hH h1
    (sc_coeff0_pos m D hp hK hε) hcp, hs, neg_neg]

/-- **Subcritical Hopf points of every fast line**: if `(X² − R²)(5K² − P''²) > 0`, below some
`ε₀ > 0` the Hopf boundary of the line of time scale `ε` contains an unstable model and every
boundary model is unstable. -/
@[tmio TM, powerlib_domain] theorem Model.atScale_mem_den_unstable (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) (hK : 0 < m.K)
    (hc : 0 < (m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2)) :
    connection% (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      (∃ D : ℝ, (0 < D ∧
        (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
            (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
            (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q) ∧
        m.atScale ε D ∈ family.den (.flow .unstable)) ∧
      ∀ D : ℝ, 0 < D →
        (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
            (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
            (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
        m.atScale ε D ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  obtain ⟨C, -, ε1, hε1, H⟩ := m.exists_atScale_hopf hp hR hK
  obtain ⟨ε2, hε2, H2⟩ := m.exists_atScale_sign_bautinFormAngle hp hR hK hc.ne'
  have hmem : ∀ ε : ℝ, 0 < ε → ε < min ε1 ε2 → ∀ D : ℝ, 0 < D →
      (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
      m.atScale ε D ∈ family.den (.flow .unstable) := by
    intro ε hε hεε0 D hD hH
    have h1 := ((H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _))).2 D hD hH).1
    have hs := H2 ε hε (lt_of_lt_of_le hεε0 (min_le_right _ _)) D hD hH
    rw [sign_pos hc] at hs
    exact mem_den_unstable_of_bautinFormAngle_neg _ (sc_physical m D hp hε hD)
      (sc_balanced m D hp hb hε) hH h1 (sc_coeff0_pos m D hp hK hε) (sign_eq_neg_one_iff.mp hs)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun ε hε hεε0 => ⟨?_, hmem ε hε hεε0⟩⟩
  obtain ⟨D, hD, hH⟩ := (H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _))).1
  exact ⟨D, ⟨hD, hH⟩, hmem ε hε hεε0 D hD hH⟩

/-- **Supercritical Hopf points of every fast line**: if `(X² − R²)(5K² − P''²) < 0`, below some
`ε₀ > 0` the Hopf boundary of the line of time scale `ε` contains a locally asymptotically
stable model and every boundary model is locally asymptotically stable. -/
@[tmio TM, powerlib_domain] theorem Model.atScale_mem_den_locallyAsymptoticallyStable
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R)
    (hK : 0 < m.K)
    (hc : (m.g.X ^ 2 - m.g.R ^ 2) * (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2) < 0) :
    connection% (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      (∃ D : ℝ, (0 < D ∧
        (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
            (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
            (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q) ∧
        m.atScale ε D ∈ family.den (.flow .locallyAsymptoticallyStable)) ∧
      ∀ D : ℝ, 0 < D →
        (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
            (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
            (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
        m.atScale ε D ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  obtain ⟨C, -, ε1, hε1, H⟩ := m.exists_atScale_hopf hp hR hK
  obtain ⟨ε2, hε2, H2⟩ := m.exists_atScale_sign_bautinFormAngle hp hR hK hc.ne
  have hmem : ∀ ε : ℝ, 0 < ε → ε < min ε1 ε2 → ∀ D : ℝ, 0 < D →
      (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
      m.atScale ε D ∈ family.den (.flow .locallyAsymptoticallyStable) := by
    intro ε hε hεε0 D hD hH
    have h1 := ((H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _))).2 D hD hH).1
    have hs := H2 ε hε (lt_of_lt_of_le hεε0 (min_le_right _ _)) D hD hH
    rw [sign_neg hc, neg_neg] at hs
    exact mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos _
      (sc_physical m D hp hε hD) (sc_balanced m D hp hb hε) hH h1 (sc_coeff0_pos m D hp hK hε)
      (sign_eq_one_iff.mp hs)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun ε hε hεε0 => ⟨?_, hmem ε hε hεε0⟩⟩
  obtain ⟨D, hD, hH⟩ := (H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _))).1
  exact ⟨D, ⟨hD, hH⟩, hmem ε hε hεε0 D hD hH⟩

/-- `ℓ₁/|q₀|²` does not depend on the critical pair at a Hopf point of the quartic. -/
@[tmio M, powerlib_domain] private theorem firstLyapunov_div_eq {m : Model}
    (h3 : 0 < m.g.coeff3) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} {q p q' p' : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hcp' : IsCriticalPair m.field 0 ω q' p') :
    firstLyapunov m.field 0 ω q' p' / ‖q' 0‖ ^ 2 = firstLyapunov m.field 0 ω q p / ‖q 0‖ ^ 2 := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (m.sq_freq_of_isCriticalPair h3.ne' hcp)
  have hc : Dynamics.CenterManifold.IsCritical (fderiv ℝ m.field 0) ω q p :=
    ⟨hcp.freq_pos, hcp.right, hcp.left, hcp.normalized⟩
  have hsq : (Polynomial.X ^ 2 + Polynomial.C ((ω : ℂ) ^ 2) : Polynomial ℂ) =
      (Polynomial.X - Polynomial.C ((ω : ℂ) * Complex.I)) *
        (Polynomial.X + Polynomial.C ((ω : ℂ) * Complex.I)) := by
    have h : ((ω : ℂ) * Complex.I) ^ 2 = -((ω : ℂ) ^ 2) := by rw [mul_pow, Complex.I_sq]; ring
    rw [show (Polynomial.X - Polynomial.C ((ω : ℂ) * Complex.I)) *
        (Polynomial.X + Polynomial.C ((ω : ℂ) * Complex.I)) =
        Polynomial.X ^ 2 - Polynomial.C ((ω : ℂ) * Complex.I) ^ 2 by ring,
      ← map_pow, h, map_neg, sub_neg_eq_add]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have hn := hcp.normalized
    simp at hn
  obtain ⟨s, hs, hq', -, hl⟩ := exists_smul_of_isCriticalPair
    (fun v hv => Dynamics.CenterManifold.IsCritical.eq_smul hc hchar hr hv)
    (fun v hv => by
      refine Dynamics.CenterManifold.eq_smul_of_charpoly
        (r := (Polynomial.X - Polynomial.C ((ω : ℂ) * Complex.I)) * r) ?_ ?_ hcp.left hp0 hv
      · rw [Matrix.charpoly_transpose, hchar, hsq, map_neg, sub_neg_eq_add]
        ring
      · rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        refine mul_ne_zero ?_ (fun h => by have := hr _ h; simp at this)
        have hω : (ω : ℂ) ≠ 0 := by exact_mod_cast hcp.freq_pos.ne'
        rw [show -((ω : ℂ) * Complex.I) - (ω : ℂ) * Complex.I =
          -(2 * ((ω : ℂ) * Complex.I)) by ring, neg_ne_zero]
        exact mul_ne_zero two_ne_zero (mul_ne_zero hω Complex.I_ne_zero))
    hcp hcp'
  rw [hl, hq', Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hs))

/-- The scaled normalised first Lyapunov coefficient `ℓ₁/(|q₀|² ε³)` of the fast line at
`(ε, y)`, `y = D/(εM)`, with the frequency `ω = √S`, `S = (y(1 + r²) − 2rκ)/(2r + ε²y)`. -/
def scaleL1 (r κ τ k ε y : ℝ) : ℝ :=
  -(r * y * (4 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * (1 + r ^ 2) * k *
        bautinFormQ (ε ^ 2 * y) r 1 (ε ^ 2 * κ) +
      τ * (2 * (ε ^ 2 * y + r) * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) - τ) *
        bautinCorr (ε ^ 2 * y) r 1 (ε ^ 2 * κ))) /
    ((2 * r + ε ^ 2 * y) ^ 4 * Real.sqrt ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) *
      (1 + r ^ 2) * k *
      (((1 + r ^ 2) - 2 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 +
          2 * r * y * ε ^ 2 - κ * ε ^ 2) ^ 2 +
        ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 *
          (2 * r + ε ^ 2 * y) ^ 2) *
      (((1 + r ^ 2) - 5 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 +
          2 * r * y * ε ^ 2 - κ * ε ^ 2) ^ 2 +
        4 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 *
          (2 * r + ε ^ 2 * y) ^ 2))

/-- The algebra of the scaled coefficient: the closed form of `ℓ₁` at the critical pair of the
fast line, divided by `|q₀|² ε³ = (a/ε)² ε³`, in the scaled variables. -/
@[tmio T, powerlib_foundation] private theorem scaleL1_identity {a ε y r κ τ k ω BQ BC : ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hω : 0 < ω) (hk : k ≠ 0)
    (hω2 : ω ^ 2 = (y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) :
    -(a ^ 2 * (1 / ε * (ε ^ 2 * y)) * (1 / ε * r) /
          ((2 * (1 / ε * r) + 1 / ε * (ε ^ 2 * y)) ^ 4 * ω * ((1 + r ^ 2) / ε ^ 2 * k) *
            angleZeroR1 (1 / ε * (ε ^ 2 * y)) (1 / ε * r) (1 / ε * 1)
              ((1 / ε) ^ 2 * (ε ^ 2 * κ)) ω *
            angleZeroR2 (1 / ε * (ε ^ 2 * y)) (1 / ε * r) (1 / ε * 1)
              ((1 / ε) ^ 2 * (ε ^ 2 * κ)) ω)) *
        (4 * ω ^ 2 * ((1 + r ^ 2) / ε ^ 2 * k) * ((1 / ε) ^ 11 * BQ) +
          (1 / ε) ^ 3 * (ε ^ 2 * τ) * (2 * (1 / ε * (ε ^ 2 * y) + 1 / ε * r) * ω ^ 2 -
            (1 / ε) ^ 3 * (ε ^ 2 * τ)) * ((1 / ε) ^ 11 * BC)) /
      ((a * (1 / ε)) ^ 2 * ε ^ 3) =
    -(r * y * (4 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * (1 + r ^ 2) * k * BQ +
        τ * (2 * (ε ^ 2 * y + r) * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) - τ) *
          BC)) /
      ((2 * r + ε ^ 2 * y) ^ 4 * Real.sqrt ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) *
        (1 + r ^ 2) * k *
        (((1 + r ^ 2) - 2 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 +
            2 * r * y * ε ^ 2 - κ * ε ^ 2) ^ 2 +
          ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 *
            (2 * r + ε ^ 2 * y) ^ 2) *
        (((1 + r ^ 2) - 5 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 +
            2 * r * y * ε ^ 2 - κ * ε ^ 2) ^ 2 +
          4 * ((y * (1 + r ^ 2) - 2 * r * κ) / (2 * r + ε ^ 2 * y)) * ε ^ 2 *
            (2 * r + ε ^ 2 * y) ^ 2)) := by
  rw [← hω2, Real.sqrt_sq hω.le]
  have hr2 : (1 + r ^ 2) ≠ 0 := by positivity
  have hε' := hε.ne'
  have hω' := hω.ne'
  unfold angleZeroR1 angleZeroR2
  have e1 : ((1 / ε * r) ^ 2 + (1 / ε * 1) ^ 2 - 2 * ω ^ 2 +
      2 * (1 / ε * r) * (1 / ε * (ε ^ 2 * y)) - (1 / ε) ^ 2 * (ε ^ 2 * κ)) ^ 2 +
      ω ^ 2 * (2 * (1 / ε * r) + 1 / ε * (ε ^ 2 * y)) ^ 2 =
      (((1 + r ^ 2) - 2 * ω ^ 2 * ε ^ 2 + 2 * r * y * ε ^ 2 - κ * ε ^ 2) ^ 2 +
        ω ^ 2 * ε ^ 2 * (2 * r + ε ^ 2 * y) ^ 2) / ε ^ 4 := by
    field_simp; ring
  have e2 : ((1 / ε * r) ^ 2 + (1 / ε * 1) ^ 2 - 5 * ω ^ 2 +
      2 * (1 / ε * r) * (1 / ε * (ε ^ 2 * y)) - (1 / ε) ^ 2 * (ε ^ 2 * κ)) ^ 2 +
      4 * ω ^ 2 * (2 * (1 / ε * r) + 1 / ε * (ε ^ 2 * y)) ^ 2 =
      (((1 + r ^ 2) - 5 * ω ^ 2 * ε ^ 2 + 2 * r * y * ε ^ 2 - κ * ε ^ 2) ^ 2 +
        4 * ω ^ 2 * ε ^ 2 * (2 * r + ε ^ 2 * y) ^ 2) / ε ^ 4 := by
    field_simp; ring
  rw [e1, e2]
  field_simp

/-- The limit value of the scaled coefficient. -/
@[tmio M, powerlib_domain] private theorem scaleL1_zero {r κ τ k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    scaleL1 r κ τ k 0 (2 * r * (k + κ) / (1 + r ^ 2)) =
      -(r * (k + κ) * (r ^ 2 - 1) * (5 * k ^ 2 - (k * r - τ) ^ 2)) /
        (Real.sqrt k * k * (1 + r ^ 2) ^ 3) := by
  have hr2 : (1 + r ^ 2) ≠ 0 := by positivity
  have hS : (2 * r * (k + κ) / (1 + r ^ 2) * (1 + r ^ 2) - 2 * r * κ) /
      (2 * r + 0 ^ 2 * (2 * r * (k + κ) / (1 + r ^ 2))) = k := by
    rw [div_mul_cancel₀ _ hr2, show (0 : ℝ) ^ 2 * (2 * r * (k + κ) / (1 + r ^ 2)) = 0 by ring,
      add_zero, show 2 * r * (k + κ) - 2 * r * κ = 2 * r * k by ring]
    field_simp
  unfold scaleL1
  rw [hS]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
    add_zero, sub_zero, bautinFormQ_zero_one, bautinCorr_zero_one]
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  field_simp
  ring

/-- The scaled coefficient is continuous at the limit point. -/
@[tmio M, powerlib_domain] private theorem continuousAt_scaleL1 {r κ τ k : ℝ} (hr : 0 < r)
    (hk : 0 < k) :
    ContinuousAt (fun p : ℝ × ℝ => scaleL1 r κ τ k p.1 p.2) (0, 2 * r * (k + κ) / (1 + r ^ 2)) := by
  set y0 := 2 * r * (k + κ) / (1 + r ^ 2) with hy0
  have hr2 : (1 + r ^ 2) ≠ 0 := by positivity
  have hd : 2 * r + (0 : ℝ) ^ 2 * y0 ≠ 0 := by simp; exact hr.ne'
  have hSc : ContinuousAt (fun p : ℝ × ℝ => (p.2 * (1 + r ^ 2) - 2 * r * κ) /
      (2 * r + p.1 ^ 2 * p.2)) (0, y0) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hd
  have hS0 : (y0 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + (0 : ℝ) ^ 2 * y0) = k := by
    rw [hy0, div_mul_cancel₀ _ hr2, show (0 : ℝ) ^ 2 * (2 * r * (k + κ) / (1 + r ^ 2)) = 0 by ring,
      add_zero, show 2 * r * (k + κ) - 2 * r * κ = 2 * r * k by ring]
    field_simp
  have hBQ : Continuous (fun p : ℝ × ℝ => bautinFormQ (p.1 ^ 2 * p.2) r 1 (p.1 ^ 2 * κ)) := by
    unfold bautinFormQ; fun_prop
  have hBC : Continuous (fun p : ℝ × ℝ => bautinCorr (p.1 ^ 2 * p.2) r 1 (p.1 ^ 2 * κ)) := by
    unfold bautinCorr; fun_prop
  have hsq := (Real.continuous_sqrt.continuousAt).comp hSc
  have hnum : ContinuousAt (fun p : ℝ × ℝ => -(r * p.2 * (4 * ((p.2 * (1 + r ^ 2) - 2 * r * κ) /
      (2 * r + p.1 ^ 2 * p.2)) * (1 + r ^ 2) * k * bautinFormQ (p.1 ^ 2 * p.2) r 1 (p.1 ^ 2 * κ) +
      τ * (2 * (p.1 ^ 2 * p.2 + r) * ((p.2 * (1 + r ^ 2) - 2 * r * κ) /
        (2 * r + p.1 ^ 2 * p.2)) - τ) * bautinCorr (p.1 ^ 2 * p.2) r 1 (p.1 ^ 2 * κ))))
      (0, y0) := by
    have := hBQ.continuousAt (x := (0, y0))
    have := hBC.continuousAt (x := (0, y0))
    fun_prop
  have hden : ContinuousAt (fun p : ℝ × ℝ => (2 * r + p.1 ^ 2 * p.2) ^ 4 *
      Real.sqrt ((p.2 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + p.1 ^ 2 * p.2)) * (1 + r ^ 2) * k *
      (((1 + r ^ 2) - 2 * ((p.2 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + p.1 ^ 2 * p.2)) * p.1 ^ 2 +
          2 * r * p.2 * p.1 ^ 2 - κ * p.1 ^ 2) ^ 2 +
        ((p.2 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + p.1 ^ 2 * p.2)) * p.1 ^ 2 *
          (2 * r + p.1 ^ 2 * p.2) ^ 2) *
      (((1 + r ^ 2) - 5 * ((p.2 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + p.1 ^ 2 * p.2)) * p.1 ^ 2 +
          2 * r * p.2 * p.1 ^ 2 - κ * p.1 ^ 2) ^ 2 +
        4 * ((p.2 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + p.1 ^ 2 * p.2)) * p.1 ^ 2 *
          (2 * r + p.1 ^ 2 * p.2) ^ 2)) (0, y0) := by
    fun_prop
  have hden0 : (2 * r + (0 : ℝ) ^ 2 * y0) ^ 4 *
      Real.sqrt ((y0 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + (0 : ℝ) ^ 2 * y0)) * (1 + r ^ 2) * k *
      (((1 + r ^ 2) - 2 * ((y0 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + (0 : ℝ) ^ 2 * y0)) *
          (0 : ℝ) ^ 2 + 2 * r * y0 * (0 : ℝ) ^ 2 - κ * (0 : ℝ) ^ 2) ^ 2 +
        ((y0 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + (0 : ℝ) ^ 2 * y0)) * (0 : ℝ) ^ 2 *
          (2 * r + (0 : ℝ) ^ 2 * y0) ^ 2) *
      (((1 + r ^ 2) - 5 * ((y0 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + (0 : ℝ) ^ 2 * y0)) *
          (0 : ℝ) ^ 2 + 2 * r * y0 * (0 : ℝ) ^ 2 - κ * (0 : ℝ) ^ 2) ^ 2 +
        4 * ((y0 * (1 + r ^ 2) - 2 * r * κ) / (2 * r + (0 : ℝ) ^ 2 * y0)) * (0 : ℝ) ^ 2 *
          (2 * r + (0 : ℝ) ^ 2 * y0) ^ 2) ≠ 0 := by
    rw [hS0]
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
      add_zero, sub_zero]
    positivity
  exact hnum.div hden hden0

/-- The limit value in the model parameters:
`L₃ = E² R X⁴ (X² − R²)(5K² − (c₀ − P_ref)²)/(K^{3/2} M^{3/2} |Z|⁸)`. -/
@[tmio M, powerlib_domain] private theorem scaleL1_limit (m : Model) (hp : Meets m .physical)
    (hR : 0 < m.g.R) (hK : 0 < m.K) :
    scaleL1 (m.g.R / m.g.X) (m.Q / m.g.M) ((m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M)
        (m.K / m.g.M) 0 (2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M)) =
      m.g.E ^ 2 * m.g.R * m.g.X ^ 4 * (m.g.X ^ 2 - m.g.R ^ 2) *
          (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2) /
        (m.K * Real.sqrt m.K * (m.g.M * Real.sqrt m.g.M) * m.g.absSq ^ 4) := by
  have hX := hp.1.X_pos
  have hZ := hp.1.absSq_pos
  have hM := hp.2.1
  have hQK : m.Q + m.K = m.g.E ^ 2 * m.g.X / m.g.absSq := by
    have h := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [Model.Q, Model.K, Network.κ] at *; linarith
  have hy : 2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M) =
      2 * (m.g.R / m.g.X) * (m.K / m.g.M + m.Q / m.g.M) / (1 + (m.g.R / m.g.X) ^ 2) := by
    rw [← add_div, add_comm m.K, hQK]
    unfold Network.absSq at hZ ⊢
    field_simp
    ring
  have hc0 : m.g.c0 = m.g.R / m.g.X * (m.Q + m.K) := by
    rw [hQK, Network.c0]; unfold Network.absSq at hZ ⊢; field_simp
  rw [hy, scaleL1_zero (div_pos hR hX) (div_pos hK hM), hc0,
    Real.sqrt_div hK.le]
  have hsK := Real.sqrt_pos.mpr hK
  have hsM := Real.sqrt_pos.mpr hM
  have eK : m.K = Real.sqrt m.K ^ 2 := (Real.sq_sqrt hK.le).symm
  have eM : m.g.M = Real.sqrt m.g.M ^ 2 := (Real.sq_sqrt hM.le).symm
  have eQ : m.Q = m.g.E ^ 2 * m.g.X / m.g.absSq - m.K := by linarith
  rw [eQ]
  unfold Network.absSq at hZ ⊢
  set sK := Real.sqrt m.K
  set sM := Real.sqrt m.g.M
  rw [eK, eM]
  field_simp
  ring

/-- **The leading coefficient of the `ε = 1/ω_b` law.** For a balanced physical model with
`R, K > 0`, `ℓ₁/(|q₀|² ε³) → L₃ = E² R X⁴ (X² − R²)(5K² − P''²)/(K^{3/2} M^{3/2} |Z|⁸)` as
`ε → 0⁺` (`P'' = c₀ − P_ref`), uniformly over the Hopf boundary dampings of the line of time scale
`ε` and over their critical pairs: `|q₀|²` normalises the critical vector to angle component `1`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_atScale_firstLyapunov_div_cube (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) (hK : 0 < m.K) {η : ℝ}
    (hη : 0 < η) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ D : ℝ, 0 < D →
      (m.atScale ε D).g.coeff3 * (m.atScale ε D).g.coeff2 (m.atScale ε D).Q *
          (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
        (m.atScale ε D).g.coeff1 (m.atScale ε D).Q ^ 2 +
          (m.atScale ε D).g.coeff3 ^ 2 * (m.atScale ε D).g.coeff0 (m.atScale ε D).Q →
      ∀ (ω : ℝ) (q p : Fin 4 → ℂ), IsCriticalPair (m.atScale ε D).field 0 ω q p →
        |firstLyapunov (m.atScale ε D).field 0 ω q p / (‖q 0‖ ^ 2 * ε ^ 3) -
          m.g.E ^ 2 * m.g.R * m.g.X ^ 4 * (m.g.X ^ 2 - m.g.R ^ 2) *
              (5 * m.K ^ 2 - (m.g.c0 - m.g.Pref) ^ 2) /
            (m.K * Real.sqrt m.K * (m.g.M * Real.sqrt m.g.M) * m.g.absSq ^ 4)| < η := by
  have hX := hp.1.X_pos
  have hZ := hp.1.absSq_pos
  have hM := hp.2.1
  have hE := hp.1.E
  obtain ⟨C, hC, ε1, hε1, H⟩ := m.exists_atScale_hopf hp hR hK
  obtain ⟨r, hr⟩ : ∃ r, r = m.g.R / m.g.X := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = m.Q / m.g.M := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m.K / m.g.M := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (m.g.Pref - m.g.R / m.g.X * m.Q) / m.g.M := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ div_pos hR hX
  have hk0 : 0 < k := hk ▸ div_pos hK hM
  have hy : 2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M) =
      2 * r * (k + q) / (1 + r ^ 2) := by
    have hQK : m.Q + m.K = m.g.E ^ 2 * m.g.X / m.g.absSq := by
      have h := m.g.syncCoeff_add_qssReactive hZ m.δ
      rw [Model.Q, Model.K, Network.κ] at *; linarith
    rw [hr, hk, hq, ← add_div, add_comm m.K, hQK]
    unfold Network.absSq at hZ ⊢
    field_simp
    ring
  have hlim := scaleL1_limit m hp hR hK
  rw [← hτ, ← hr, ← hq, ← hk, hy] at hlim
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp (continuousAt_scaleL1 (κ := q) (τ := τ)
    hr0 hk0) η hη
  rw [hlim] at hcont
  set yh := 2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / (m.g.absSq ^ 2 * m.g.M) with hyh
  have hyh0 : 0 < yh := by rw [hyh]; positivity
  refine ⟨min ε1 (min 1 (min δ (δ / (1 + yh * C)))), by positivity,
    fun ε hε hεε0 D hD hH ω qv pv hcp => ?_⟩
  have hεε1 : ε < ε1 := lt_of_lt_of_le hεε0 (min_le_left _ _)
  have hε1' : ε < 1 := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ : ε < δ := lt_of_lt_of_le hεε0
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεη : ε < δ / (1 + yh * C) := lt_of_lt_of_le hεε0
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨h1, hlo, hhi⟩ := (H ε hε hεε1).2 D hD hH
  have hDl : m.DlineAt ε = ε * m.g.M * yh := by rw [Model.DlineAt, hyh]; exact alg_dl hM.ne'
  rw [hDl] at hlo hhi
  obtain ⟨-, hyc⟩ := scaled_close hε hε1' hC hyh0 hM hεη hlo hhi
  -- the critical pair of the closed form
  have hp' := sc_physical m D hp hε hD
  have hb' := sc_balanced m D hp hb hε
  have h0 := sc_coeff0_pos m D hp hK hε
  have e := sc_coeffs m D hp hε
  have h3 : 0 < (m.atScale ε D).g.coeff3 := by rw [e.1]; positivity
  have hω := hcp.freq_pos
  have hω2 := (m.atScale ε D).sq_freq_of_isCriticalPair h3.ne' hcp
  have hcrit := Model.isCriticalPair_crit hp' hb' hH hω hω2
  have hratio := firstLyapunov_div_eq h3 h1 h0 hH hcrit hcp
  obtain ⟨y, hydef⟩ : ∃ y, y = D / (ε * m.g.M) := ⟨_, rfl⟩
  have hS : ω ^ 2 = (y * (1 + r ^ 2) - 2 * r * q) / (2 * r + ε ^ 2 * y) := by
    rw [hω2, e.1, e.2.2.1, ← hr, ← hq, hydef]
    field_simp
  have hq0 : ‖(m.atScale ε D).critQ ω 0‖ ^ 2 =
      ((m.atScale ε D).g.E / (m.atScale ε D).g.M * (1 / ε)) ^ 2 := by
    have : (m.atScale ε D).critQ ω 0 =
        (((m.atScale ε D).g.E / (m.atScale ε D).g.M * (1 / ε) : ℝ) : ℂ) := by
      simp [Model.critQ, rotC, angleZeroQ, Model.atScale]
    rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have a1 : (m.atScale ε D).g.D / (m.atScale ε D).g.M = 1 / ε * (ε ^ 2 * y) :=
    (alg_a1 hε.ne' hM.ne' hydef).symm
  have a2 : (m.atScale ε D).g.R / (m.atScale ε D).g.L = 1 / ε * r := by
    rw [hr]; exact (alg_a2 hε.ne' hX.ne').symm
  have a3 : (m.atScale ε D).g.ω0 = 1 / ε * 1 := by rw [mul_one]; rfl
  have a4 : (m.atScale ε D).Q / (m.atScale ε D).g.M = (1 / ε) ^ 2 * (ε ^ 2 * q) := by
    rw [sc_Q m D hε.ne' hZ.ne', hq]; exact (alg_a4 hε.ne').symm
  have a5 : (m.atScale ε D).angleShift = (1 / ε) ^ 3 * (ε ^ 2 * τ) := by
    rw [sc_angleShift m D hp hε, hτ]
  have a6 : (m.atScale ε D).g.coeff0 (m.atScale ε D).Q = (1 + r ^ 2) / ε ^ 2 * k := by
    rw [e.2.2.2, ← hr, ← hk]
  have key : firstLyapunov (m.atScale ε D).field 0 ω qv pv / (‖qv 0‖ ^ 2 * ε ^ 3) =
      scaleL1 r q τ k ε y := by
    rw [← div_div, hratio, Model.firstLyapunov_crit hp' hb' hH h0 hω hω2, hq0, a1, a2, a3, a4,
      a5, a6, bautinFormQ_scale, bautinCorr_scale, div_div]
    exact scaleL1_identity (div_pos hE hM).ne' hε hω hk0.ne' hS
  rw [key]
  have hd : dist (ε, y) ((0 : ℝ), 2 * r * (k + q) / (1 + r ^ 2)) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hε, ← hy, hydef]
    exact max_lt hεδ hyc
  have hc := hcont hd
  rwa [Real.dist_eq] at hc

end VSM
end powerlib.GFM.Line
