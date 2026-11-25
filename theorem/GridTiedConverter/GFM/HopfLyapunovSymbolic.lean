import theorem.GridTiedConverter.GFM.HopfLyapunovCurrent
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.Basic

/-! # The symbolic boundary between sub- and supercritical Hopf points of the VSM on a line

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* The slice: the zero-current models `Line.VSM.zeroCurrent E R L ω₀ M D` (`V = E`, `P_ref = 0`,
  `δ* = 0`; no line current at the operating point, balanced for every parameter set), physical
  range `E, L, ω₀, M, D > 0`, `R ≥ 0`. It is the instance `V = E` of the slice `δ* = 0` of
  `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean` (`zeroCurrent_eq_angleZero`), whose laws
  give the results here; it contains `Line.VSM.hopfWitness`, `Line.VSM.hopfWitnessSup` and every
  point of `Line.VSM.bautinPath`. Not covered: `δ* ≠ 0`.
* Notation: `a = E/M`, `b = E/L`, `d = D/M`, `σ = R/L`, `ρ = σ² + ω₀²`; the monic quartic has
  `a₃ = 2σ + d`, `a₂ = ρ + 2σd`, `a₁ = dρ`, `a₀ = a b ω₀`.
* Level: exact identities and signs for all parameters of the slice (no sample points), and
  Lyapunov instability / local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the operating point. Not stated: the bifurcating cycles, the
  stability of the degenerate points `𝔅 = 0` themselves (second Lyapunov coefficient), the
  `ε = 1/ω_b` law of the source note.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, the VSM without filter on a dynamic
R–L line); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4;
Descartes' rule of signs (`Polynomial.roots_countP_pos_le_signVariations`). The closed forms were
derived with SymPy in exact rational arithmetic (exact polynomial division, factorisation over
`ℚ`, exact real-root isolation; untrusted discovery); every identity is proved here by
`linear_combination` or `ring` with its polynomial certificate.

Results.
* The slice: `Line.VSM.zeroCurrent`, `zeroCurrent_point`, `zeroCurrent_balanced`, `zeroCurrent_Q`,
  `zeroCurrent_coeffs`, `zeroCurrent_eq_angleZero`.
* **The Hopf boundary in closed form**: `zeroCurrent_hopf_iff` (`a₃a₂a₁ = a₁² + a₃²a₀` iff
  `2σ d ρ (ρ + 2σd + d²) L M = (2σ + d)² E² ω₀`), `zeroCurrent_hopf_iff_inertia` (iff
  `M = hopfInertia E R L ω₀ (D/M) = E² ω₀ (2σ + d)²/(2σ d ρ (ρ + 2σd + d²) L)`: the inertia solved
  from the damping ratio), the explicit boundary family `zeroCurrentHopf E R L ω₀ d`
  (`zeroCurrentHopf_meets`), `zeroCurrent_R_pos`.
* **`ℓ₁` in closed form** at the critical pair (`angleZeroQ`, `angleZeroP`) with `κ = 0`:
  `zeroCurrent_firstLyapunov_eq_bautinForm`,
  `ℓ₁ = −4 a² d σ ω 𝔅(D/M, R/L, ω₀) / ((2σ + d)⁴ |r(iω)|² |r(2iω)|²)` with the Bautin form
  `𝔅 = bautinForm` (degree 11, irreducible; `bautinFormQ_zero`: `𝔅_Q(·, 0) = 𝔅`), and
  `zeroCurrent_firstLyapunov`, `ℓ₁ = a² d⁴ N(ω², σ², ω₀²) / (16 σ³ ω⁵ |r(iω)|² |r(2iω)|²)`, the
  frequency-normalised numerator `N = ellNum` (`ellNum_mul_eq`:
  `(2σ + d)⁷ N(ω², σ², ω₀²) = −64 σ⁴ ρ³ 𝔅(d, σ, ω₀)`).
* **The symbolic boundary between sub- and supercritical**: `zeroCurrent_sign_firstLyapunov`
  (every critical pair of every physical boundary model: `sign ℓ₁ = −sign 𝔅(D/M, R/L, ω₀)`).
* **The Bautin set `{𝔅 = 0}` exactly** (section docstring): `bautinForm_eq_coeffs`,
  `bautinPolyY` (the quartic in `ω₀²`), `bautinPolyY_countP_pos_le` (Descartes: at most two
  positive roots when `bautinHigh < 0`), `bautinForm_homogeneous`, and the description in
  `ω₀ > 0` for fixed `d, σ > 0`: `bautinSet_eq_empty` (`bautinLow ≥ 0`, i.e. `d ≥ x₀σ`),
  `bautinSet_eq_singleton` (`bautinLow < 0 ≤ bautinHigh`: one point `ω_low ∈ (0, σ)`),
  `bautinSet_eq_pair` (`bautinHigh < 0`, i.e. `d < x₄σ`: two points `ω_low ∈ (0, σ)`,
  `ω_high ∈ (σ, ∞)`), each with the supercritical set `𝔅 > 0` (`ω_low < ω₀ < ω_high`, resp.
  `ω₀ > ω_low`); the thresholds `bautinLow_neg`, `bautinLow_pos` (`x₀ ∈ (7/5, 71/50)`),
  `bautinHigh_neg`, `bautinHigh_pos` (`x₄ ∈ (3/4, 4/5)`), `bautinForm_self_pos` (`X = R` is
  supercritical), `bautinForm_pos_of_bautinLow`, `exists_bautinForm_neg`,
  `forall_bautinForm_pos_iff`, `bautinForm_pos_of_one_le`, `bautinMid_pos`,
  `bautinC3_pos_of_bautinHigh`.

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.zeroCurrent_mem_den_locallyAsymptoticallyStable` (`𝔅 > 0`) and
  `Line.VSM.zeroCurrent_mem_den_unstable` (`𝔅 < 0`): the instances `V = E` of
  `Line.VSM.angleZero_mem_den_locallyAsymptoticallyStable`, `Line.VSM.angleZero_mem_den_unstable`.
* `Line.VSM.zeroCurrentHopf_mem_den_locallyAsymptoticallyStable`,
  `Line.VSM.zeroCurrentHopf_mem_den_unstable` (the explicit boundary family),
  `Line.VSM.zeroCurrent_mem_den_locallyAsymptoticallyStable_of_bautinLow` (`D/M ≥ x₀ R/L`),
  `Line.VSM.zeroCurrent_mem_den_locallyAsymptoticallyStable_of_X_eq_R` (`ω₀ L = R`).
* Instances proved in their modules by exact arithmetic at points:
  `Line.VSM.hopfWitness_mem_den_unstable`,
  `Line.VSM.hopfWitnessSup_mem_den_locallyAsymptoticallyStable`,
  `Line.VSM.bautinPath_mem_den_locallyAsymptoticallyStable`, `Line.VSM.bautinPath_mem_den_unstable`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Matrix
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The zero-current slice -/

/-- **The zero-current models**: `E = V`, `P_ref = 0`, `δ* = 0`, with line resistance `R`,
inductance `L`, nominal frequency `ω₀ = w`, inertia `M` and damping `D`. -/
def zeroCurrent (E R L w M D : ℝ) : Model := ⟨⟨⟨E, E, R, L, w⟩, M, D, 0⟩, 0⟩

/-- The operating point of a zero-current model carries no current. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_point (E R L w M D : ℝ) :
    (zeroCurrent E R L w M D).point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, zeroCurrent, Network.is]

/-- Every zero-current model is balanced. Satisfaction of the requirements. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_balanced (E R L w M D : ℝ) :
    Meets (zeroCurrent E R L w M D) .balanced := by
  norm_num [Meets, zeroCurrent, Network.qssPower, Network.is, Network.power_eq]

/-- No reactive power at the operating point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_Q (E R L w M D : ℝ) :
    (zeroCurrent E R L w M D).Q = 0 := by
  norm_num [Model.Q, Network.qssReactive, zeroCurrent, Network.is, Network.reactive_eq]

/-- The coefficients of the monic quartic: `a₃ = 2σ + d`, `a₂ = ρ + 2σd`, `a₁ = dρ`, `a₀ = abω₀`
(`σ = R/L`, `d = D/M`, `a = E/M`, `b = E/L`, `ρ = σ² + ω₀²`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_coeffs {E R L w M D : ℝ} (hL : L ≠ 0) :
    (zeroCurrent E R L w M D).g.coeff3 = 2 * (R / L) + D / M ∧
      (zeroCurrent E R L w M D).g.coeff2 (zeroCurrent E R L w M D).Q =
        (R / L) ^ 2 + w ^ 2 + 2 * (R / L) * (D / M) ∧
      (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q =
        D / M * ((R / L) ^ 2 + w ^ 2) ∧
      (zeroCurrent E R L w M D).g.coeff0 (zeroCurrent E R L w M D).Q = E / M * (E / L) * w := by
  rw [zeroCurrent_Q]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [coeff3, coeff2, coeff1, coeff0, zeroCurrent, Network.ρ, Network.σ, Network.X] <;>
    field_simp <;> ring

/-- **The zero-current slice is the instance `V = E` of the slice `δ* = 0`**
(`Line.VSM.angleZero`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_eq_angleZero (E R L w M D : ℝ) :
    zeroCurrent E R L w M D = angleZero E E R L w M D := by
  simp [zeroCurrent, angleZero]

/-! ## The Hopf boundary in closed form -/

/-- **The Hopf boundary of the slice**: `a₃a₂a₁ = a₁² + a₃²a₀` iff
`2σ d ρ (ρ + 2σd + d²) L M = (2σ + d)² E² ω₀` (`a₃a₂ − a₁ = 2σ(ρ + 2σd + d²)`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_hopf_iff {E R L w M D : ℝ} (hL : L ≠ 0)
    (hM : M ≠ 0) :
    (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q ↔
      2 * (R / L) * (D / M) * ((R / L) ^ 2 + w ^ 2) *
          ((R / L) ^ 2 + w ^ 2 + 2 * (R / L) * (D / M) + (D / M) ^ 2) * L * M =
        (2 * (R / L) + D / M) ^ 2 * E ^ 2 * w := by
  obtain ⟨h3, h2, h1, h0⟩ := zeroCurrent_coeffs (E := E) (R := R) (w := w) (M := M) (D := D) hL
  rw [h3, h2, h1, h0]
  have hLM : L * M ≠ 0 := mul_ne_zero hL hM
  have key : (2 * (R / L) + D / M) * ((R / L) ^ 2 + w ^ 2 + 2 * (R / L) * (D / M)) *
        (D / M * ((R / L) ^ 2 + w ^ 2)) - ((D / M * ((R / L) ^ 2 + w ^ 2)) ^ 2 +
        (2 * (R / L) + D / M) ^ 2 * (E / M * (E / L) * w)) =
      (2 * (R / L) * (D / M) * ((R / L) ^ 2 + w ^ 2) *
          ((R / L) ^ 2 + w ^ 2 + 2 * (R / L) * (D / M) + (D / M) ^ 2) * L * M -
        (2 * (R / L) + D / M) ^ 2 * E ^ 2 * w) / (L * M) := by
    field_simp
    ring
  constructor
  · intro h
    rw [h, sub_self, eq_comm, div_eq_zero_iff] at key
    exact sub_eq_zero.mp (key.resolve_right hLM)
  · intro h
    rw [← sub_eq_zero, key, h, sub_self, zero_div]

/-- The inertia of the boundary point with damping ratio `d = D/M`:
`M(d) = E² ω₀ (2σ + d)²/(2σ d ρ (ρ + 2σd + d²) L)`. -/
def hopfInertia (E R L w d : ℝ) : ℝ :=
  E ^ 2 * w * (2 * (R / L) + d) ^ 2 /
    (2 * (R / L) * d * ((R / L) ^ 2 + w ^ 2) * ((R / L) ^ 2 + w ^ 2 + 2 * (R / L) * d + d ^ 2) * L)

/-- **The explicit parametrisation of the boundary**: a physical zero-current model is on the
Hopf boundary iff its inertia is `M = M(D/M)` (`hopfInertia`); for every `E, R, L, ω₀ > 0` and
every ratio `d > 0` the model `zeroCurrent E R L ω₀ M(d) (d M(d))` is the boundary point with
`D/M = d`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_hopf_iff_inertia {E R L w M D : ℝ} (hR : 0 < R)
    (hL : 0 < L) (hw : 0 < w) (hM : 0 < M) (hD : 0 < D) :
    ((zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q) ↔ M = hopfInertia E R L w (D / M) := by
  rw [zeroCurrent_hopf_iff hL.ne' hM.ne', hopfInertia]
  have hpos : 0 < 2 * (R / L) * (D / M) * ((R / L) ^ 2 + w ^ 2) *
      ((R / L) ^ 2 + w ^ 2 + 2 * (R / L) * (D / M) + (D / M) ^ 2) * L := by positivity
  rw [eq_div_iff hpos.ne']
  constructor <;> intro h <;> linarith

/-- **The boundary forces a resistive line**: a physical zero-current model on the Hopf boundary
has `R > 0` (`angleZero_R_pos`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_R_pos {E R L w M D : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q) : 0 < R := by
  rw [zeroCurrent_eq_angleZero] at hp hH
  exact angleZero_R_pos hp hH

/-! ## The polynomials of the closed form -/

/-- **The numerator of `ℓ₁` on the zero-current boundary** in the frequency-normalised variables
`X = ω²`, `T = σ²`, `W = ω₀²` (homogeneous of degree 7, irreducible over `ℚ`; at `X = W = 1` it is
`T²(T⁵ + 12T⁴ − 22T³ − 132T² − 160T − 64)`, the polynomial of `Line.VSM.bautinNum`). -/
def ellNum (X T W : ℝ) : ℝ :=
  -35 * X ^ 7 + 45 * X ^ 6 * T + 153 * X ^ 6 * W + 123 * X ^ 5 * T ^ 2 - 114 * X ^ 5 * T * W - 281 *
    X ^ 5 * W ^ 2 - 49 * X ^ 4 * T ^ 3 - 371 * X ^ 4 * T ^ 2 * W + 73 * X ^ 4 * T * W ^ 2 + 299 *
    X ^ 4 * W ^ 3 - 101 * X ^ 3 * T ^ 4 + 12 * X ^ 3 * T ^ 3 * W + 330 * X ^ 3 * T ^ 2 * W ^ 2 - 68
    * X ^ 3 * T * W ^ 3 - 221 * X ^ 3 * W ^ 4 + 3 * X ^ 2 * T ^ 5 + 107 * X ^ 2 * T ^ 4 * W + 70 *
    X ^ 2 * T ^ 3 * W ^ 2 + 14 * X ^ 2 * T ^ 2 * W ^ 3 + 167 * X ^ 2 * T * W ^ 4 + 119 * X ^ 2 *
    W ^ 5 + 13 * X * T ^ 6 - 10 * X * T ^ 5 * W - 113 * X * T ^ 4 * W ^ 2 - 188 * X * T ^ 3 * W ^ 3
    - 181 * X * T ^ 2 * W ^ 4 - 122 * X * T * W ^ 5 - 39 * X * W ^ 6 + T ^ 7 - T ^ 6 * W - 15 *
    T ^ 5 * W ^ 2 - 25 * T ^ 4 * W ^ 3 - 5 * T ^ 3 * W ^ 4 + 21 * T ^ 2 * W ^ 5 + 19 * T * W ^ 6 + 5
    * W ^ 7

/-- **The Bautin form** of the zero-current slice in the model parameters `d = D/M`, `σ = R/L`,
`w = ω₀` (homogeneous of degree 11; `ℓ₁` has the sign of `−bautinForm`). -/
def bautinForm (d σ w : ℝ) : ℝ :=
  d ^ 7 * σ ^ 2 * w ^ 2 + d ^ 7 * w ^ 4 + 5 * d ^ 6 * σ ^ 5 + 12 * d ^ 6 * σ ^ 3 * w ^ 2 + 9 * d ^ 6
    * σ * w ^ 4 + 24 * d ^ 5 * σ ^ 6 + 40 * d ^ 5 * σ ^ 4 * w ^ 2 + 36 * d ^ 5 * σ ^ 2 * w ^ 4 + 4 *
    d ^ 5 * w ^ 6 + 16 * d ^ 4 * σ ^ 7 + 24 * d ^ 4 * σ ^ 5 * w ^ 2 + 76 * d ^ 4 * σ ^ 3 * w ^ 4 +
    20 * d ^ 4 * σ * w ^ 6 - 36 * d ^ 3 * σ ^ 8 + 37 * d ^ 3 * σ ^ 6 * w ^ 2 + 215 * d ^ 3 * σ ^ 4 *
    w ^ 4 + 87 * d ^ 3 * σ ^ 2 * w ^ 6 + 9 * d ^ 3 * w ^ 8 - 51 * d ^ 2 * σ ^ 9 + 98 * d ^ 2 * σ ^ 7
    * w ^ 2 + 242 * d ^ 2 * σ ^ 5 * w ^ 4 + 66 * d ^ 2 * σ ^ 3 * w ^ 6 + 5 * d ^ 2 * σ * w ^ 8 - 20
    * d * σ ^ 10 + 64 * d * σ ^ 8 * w ^ 2 + 96 * d * σ ^ 6 * w ^ 4 + 16 * d * σ ^ 4 * w ^ 6 + 4 * d
    * σ ^ 2 * w ^ 8 - 2 * σ ^ 11 + 8 * σ ^ 9 * w ^ 2 + 12 * σ ^ 7 * w ^ 4 - 8 * σ ^ 5 * w ^ 6 - 10 *
    σ ^ 3 * w ^ 8

/-- **From the frequency to the model parameters**: if `d(σ² + ω₀² − ω²) = 2σω²` (that is
`ω² = dρ/(2σ + d)`), then `(2σ + d)⁷ N(ω², σ², ω₀²) = −64 σ⁴ ρ³ 𝔅(d, σ, ω₀)` (exact polynomial
division, the quotient is the certificate). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem ellNum_mul_eq {d σ w ω : ℝ}
    (h : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * ω ^ 2) :
    (2 * σ + d) ^ 7 * ellNum (ω ^ 2) (σ ^ 2) (w ^ 2) =
      -64 * σ ^ 4 * (σ ^ 2 + w ^ 2) ^ 3 * bautinForm d σ w := by
  unfold ellNum bautinForm
  linear_combination (d ^ 6 * σ ^ 12 + 62 * d ^ 6 * σ ^ 10 * w ^ 2 + 14 * d ^ 6 * σ ^ 10 * ω ^ 2 +
    179 * d ^ 6 * σ ^ 8 * w ^ 4 + 38 * d ^ 6 * σ ^ 8 * w ^ 2 * ω ^ 2 + 17 * d ^ 6 * σ ^ 8 * ω ^ 4 +
    180 * d ^ 6 * σ ^ 6 * w ^ 6 + 28 * d ^ 6 * σ ^ 6 * w ^ 4 * ω ^ 2 + 128 * d ^ 6 * σ ^ 6 * w ^ 2 *
    ω ^ 4 - 84 * d ^ 6 * σ ^ 6 * ω ^ 6 + 71 * d ^ 6 * σ ^ 4 * w ^ 8 - 36 * d ^ 6 * σ ^ 4 * w ^ 6 *
    ω ^ 2 - 30 * d ^ 6 * σ ^ 4 * w ^ 4 * ω ^ 4 + 224 * d ^ 6 * σ ^ 4 * w ^ 2 * ω ^ 6 - 133 * d ^ 6 *
    σ ^ 4 * ω ^ 8 + 14 * d ^ 6 * σ ^ 2 * w ^ 10 - 74 * d ^ 6 * σ ^ 2 * w ^ 8 * ω ^ 2 + 8 * d ^ 6 *
    σ ^ 2 * w ^ 6 * ω ^ 4 + 76 * d ^ 6 * σ ^ 2 * w ^ 4 * ω ^ 6 - 14 * d ^ 6 * σ ^ 2 * w ^ 2 * ω ^ 8
    - 10 * d ^ 6 * σ ^ 2 * ω ^ 10 + 5 * d ^ 6 * w ^ 12 - 34 * d ^ 6 * w ^ 10 * ω ^ 2 + 85 * d ^ 6 *
    w ^ 8 * ω ^ 4 - 136 * d ^ 6 * w ^ 6 * ω ^ 6 + 163 * d ^ 6 * w ^ 4 * ω ^ 8 - 118 * d ^ 6 * w ^ 2
    * ω ^ 10 + 35 * d ^ 6 * ω ^ 12 + 334 * d ^ 5 * σ ^ 13 + 1380 * d ^ 5 * σ ^ 11 * w ^ 2 + 518 *
    d ^ 5 * σ ^ 11 * ω ^ 2 + 2250 * d ^ 5 * σ ^ 9 * w ^ 4 + 846 * d ^ 5 * σ ^ 9 * w ^ 2 * ω ^ 2 +
    588 * d ^ 5 * σ ^ 9 * ω ^ 4 + 1752 * d ^ 5 * σ ^ 7 * w ^ 6 + 180 * d ^ 5 * σ ^ 7 * w ^ 4 * ω ^ 2
    + 1832 * d ^ 5 * σ ^ 7 * w ^ 2 * ω ^ 4 - 792 * d ^ 5 * σ ^ 7 * ω ^ 6 + 674 * d ^ 5 * σ ^ 5 *
    w ^ 8 - 700 * d ^ 5 * σ ^ 5 * w ^ 6 * ω ^ 2 - 616 * d ^ 5 * σ ^ 5 * w ^ 4 * ω ^ 4 + 3048 * d ^ 5
    * σ ^ 5 * w ^ 2 * ω ^ 6 - 1646 * d ^ 5 * σ ^ 5 * ω ^ 8 + 196 * d ^ 5 * σ ^ 3 * w ^ 10 - 1018 *
    d ^ 5 * σ ^ 3 * w ^ 8 * ω ^ 2 + 40 * d ^ 5 * σ ^ 3 * w ^ 6 * ω ^ 4 + 896 * d ^ 5 * σ ^ 3 * w ^ 4
    * ω ^ 6 - 52 * d ^ 5 * σ ^ 3 * w ^ 2 * ω ^ 8 - 190 * d ^ 5 * σ ^ 3 * ω ^ 10 + 70 * d ^ 5 * σ *
    w ^ 12 - 466 * d ^ 5 * σ * w ^ 10 * ω ^ 2 + 1132 * d ^ 5 * σ * w ^ 8 * ω ^ 4 - 1792 * d ^ 5 * σ
    * w ^ 6 * ω ^ 6 + 2122 * d ^ 5 * σ * w ^ 4 * ω ^ 8 - 1486 * d ^ 5 * σ * w ^ 2 * ω ^ 10 + 420 *
    d ^ 5 * σ * ω ^ 12 + 1620 * d ^ 4 * σ ^ 14 + 5464 * d ^ 4 * σ ^ 12 * w ^ 2 + 3380 * d ^ 4 *
    σ ^ 12 * ω ^ 2 + 7868 * d ^ 4 * σ ^ 10 * w ^ 4 + 4004 * d ^ 4 * σ ^ 10 * w ^ 2 * ω ^ 2 + 4668 *
    d ^ 4 * σ ^ 10 * ω ^ 4 + 6416 * d ^ 4 * σ ^ 8 * w ^ 6 - 1128 * d ^ 4 * σ ^ 8 * w ^ 4 * ω ^ 2 +
    10016 * d ^ 4 * σ ^ 8 * w ^ 2 * ω ^ 4 - 2640 * d ^ 4 * σ ^ 8 * ω ^ 6 + 3404 * d ^ 4 * σ ^ 6 *
    w ^ 8 - 4744 * d ^ 4 * σ ^ 6 * w ^ 6 * ω ^ 2 - 4904 * d ^ 4 * σ ^ 6 * w ^ 4 * ω ^ 4 + 17328 *
    d ^ 4 * σ ^ 6 * w ^ 2 * ω ^ 6 - 8340 * d ^ 4 * σ ^ 6 * ω ^ 8 + 1432 * d ^ 4 * σ ^ 4 * w ^ 10 -
    5708 * d ^ 4 * σ ^ 4 * w ^ 8 * ω ^ 2 - 64 * d ^ 4 * σ ^ 4 * w ^ 6 * ω ^ 4 + 4256 * d ^ 4 * σ ^ 4
    * w ^ 4 * ω ^ 6 + 600 * d ^ 4 * σ ^ 4 * w ^ 2 * ω ^ 8 - 1300 * d ^ 4 * σ ^ 4 * ω ^ 10 + 420 *
    d ^ 4 * σ ^ 2 * w ^ 12 - 2716 * d ^ 4 * σ ^ 2 * w ^ 10 * ω ^ 2 + 6348 * d ^ 4 * σ ^ 2 * w ^ 8 *
    ω ^ 4 - 9952 * d ^ 4 * σ ^ 2 * w ^ 6 * ω ^ 6 + 11580 * d ^ 4 * σ ^ 2 * w ^ 4 * ω ^ 8 - 7780 *
    d ^ 4 * σ ^ 2 * w ^ 2 * ω ^ 10 + 2100 * d ^ 4 * σ ^ 2 * ω ^ 12 + 1304 * d ^ 3 * σ ^ 15 + 3024 *
    d ^ 3 * σ ^ 13 * w ^ 2 + 8184 * d ^ 3 * σ ^ 13 * ω ^ 2 + 5320 * d ^ 3 * σ ^ 11 * w ^ 4 + 2968 *
    d ^ 3 * σ ^ 11 * w ^ 2 * ω ^ 2 + 15784 * d ^ 3 * σ ^ 11 * ω ^ 4 + 9184 * d ^ 3 * σ ^ 9 * w ^ 6 -
    13552 * d ^ 3 * σ ^ 9 * w ^ 4 * ω ^ 2 + 25152 * d ^ 3 * σ ^ 9 * w ^ 2 * ω ^ 4 - 3160 * d ^ 3 *
    σ ^ 9 * ω ^ 6 + 9384 * d ^ 3 * σ ^ 7 * w ^ 8 - 17072 * d ^ 3 * σ ^ 7 * w ^ 6 * ω ^ 2 - 21360 *
    d ^ 3 * σ ^ 7 * w ^ 4 * ω ^ 4 + 51704 * d ^ 3 * σ ^ 7 * w ^ 2 * ω ^ 6 - 22160 * d ^ 3 * σ ^ 7 *
    ω ^ 8 + 5200 * d ^ 3 * σ ^ 5 * w ^ 10 - 17416 * d ^ 3 * σ ^ 5 * w ^ 8 * ω ^ 2 - 1280 * d ^ 3 *
    σ ^ 5 * w ^ 6 * ω ^ 4 + 9528 * d ^ 3 * σ ^ 5 * w ^ 4 * ω ^ 6 + 4640 * d ^ 3 * σ ^ 5 * w ^ 2 *
    ω ^ 8 - 4400 * d ^ 3 * σ ^ 5 * ω ^ 10 + 1400 * d ^ 3 * σ ^ 3 * w ^ 12 - 8680 * d ^ 3 * σ ^ 3 *
    w ^ 10 * ω ^ 2 + 19208 * d ^ 3 * σ ^ 3 * w ^ 8 * ω ^ 4 - 29976 * d ^ 3 * σ ^ 3 * w ^ 6 * ω ^ 6 +
    33840 * d ^ 3 * σ ^ 3 * w ^ 4 * ω ^ 8 - 21680 * d ^ 3 * σ ^ 3 * w ^ 2 * ω ^ 10 + 5600 * d ^ 3 *
    σ ^ 3 * ω ^ 12 - 1744 * d ^ 2 * σ ^ 16 - 3360 * d ^ 2 * σ ^ 14 * w ^ 2 + 8144 * d ^ 2 * σ ^ 14 *
    ω ^ 2 + 8912 * d ^ 2 * σ ^ 12 * w ^ 4 - 11056 * d ^ 2 * σ ^ 12 * w ^ 2 * ω ^ 2 + 26192 * d ^ 2 *
    σ ^ 12 * ω ^ 4 + 28736 * d ^ 2 * σ ^ 10 * w ^ 6 - 32672 * d ^ 2 * σ ^ 10 * w ^ 4 * ω ^ 2 + 28608
    * d ^ 2 * σ ^ 10 * w ^ 2 * ω ^ 4 + 1200 * d ^ 2 * σ ^ 10 * ω ^ 6 + 29392 * d ^ 2 * σ ^ 8 * w ^ 8
    - 25504 * d ^ 2 * σ ^ 8 * w ^ 6 * ω ^ 2 - 49184 * d ^ 2 * σ ^ 8 * w ^ 4 * ω ^ 4 + 84432 * d ^ 2
    * σ ^ 8 * w ^ 2 * ω ^ 6 - 32560 * d ^ 2 * σ ^ 8 * ω ^ 8 + 14560 * d ^ 2 * σ ^ 6 * w ^ 10 - 27696
    * d ^ 2 * σ ^ 6 * w ^ 8 * ω ^ 2 - 2624 * d ^ 2 * σ ^ 6 * w ^ 6 * ω ^ 4 + 8464 * d ^ 2 * σ ^ 6 *
    w ^ 4 * ω ^ 6 + 12640 * d ^ 2 * σ ^ 6 * w ^ 2 * ω ^ 8 - 8000 * d ^ 2 * σ ^ 6 * ω ^ 10 + 3376 *
    d ^ 2 * σ ^ 4 * w ^ 12 - 15664 * d ^ 2 * σ ^ 4 * w ^ 10 * ω ^ 2 + 33616 * d ^ 2 * σ ^ 4 * w ^ 8
    * ω ^ 4 - 51728 * d ^ 2 * σ ^ 4 * w ^ 6 * ω ^ 6 + 55760 * d ^ 2 * σ ^ 4 * w ^ 4 * ω ^ 8 - 33920
    * d ^ 2 * σ ^ 4 * w ^ 2 * ω ^ 10 + 8400 * d ^ 2 * σ ^ 4 * ω ^ 12 - 2592 * d * σ ^ 17 - 1600 * d
    * σ ^ 15 * w ^ 2 + 2656 * d * σ ^ 15 * ω ^ 2 + 16032 * d * σ ^ 13 * w ^ 4 - 17696 * d * σ ^ 13 *
    w ^ 2 * ω ^ 2 + 20960 * d * σ ^ 13 * ω ^ 4 + 33408 * d * σ ^ 11 * w ^ 6 - 24384 * d * σ ^ 11 *
    w ^ 4 * ω ^ 2 + 11136 * d * σ ^ 11 * w ^ 2 * ω ^ 4 + 5472 * d * σ ^ 11 * ω ^ 6 + 28960 * d *
    σ ^ 9 * w ^ 8 - 11072 * d * σ ^ 9 * w ^ 6 * ω ^ 2 - 53824 * d * σ ^ 9 * w ^ 4 * ω ^ 4 + 70944 *
    d * σ ^ 9 * w ^ 2 * ω ^ 6 - 25056 * d * σ ^ 9 * ω ^ 8 + 14272 * d * σ ^ 7 * w ^ 10 - 22816 * d *
    σ ^ 7 * w ^ 8 * ω ^ 2 + 1152 * d * σ ^ 7 * w ^ 6 * ω ^ 4 - 1376 * d * σ ^ 7 * w ^ 4 * ω ^ 6 +
    15552 * d * σ ^ 7 * w ^ 2 * ω ^ 8 - 7520 * d * σ ^ 7 * ω ^ 10 + 3680 * d * σ ^ 5 * w ^ 12 -
    15776 * d * σ ^ 5 * w ^ 10 * ω ^ 2 + 32864 * d * σ ^ 5 * w ^ 8 * ω ^ 4 - 48416 * d * σ ^ 5 *
    w ^ 6 * ω ^ 6 + 49056 * d * σ ^ 5 * w ^ 4 * ω ^ 8 - 28256 * d * σ ^ 5 * w ^ 2 * ω ^ 10 + 6720 *
    d * σ ^ 5 * ω ^ 12 - 832 * σ ^ 18 + 640 * σ ^ 16 * w ^ 2 - 192 * σ ^ 16 * ω ^ 2 + 7232 * σ ^ 14
    * w ^ 4 - 6848 * σ ^ 14 * w ^ 2 * ω ^ 2 + 6464 * σ ^ 14 * ω ^ 4 + 12032 * σ ^ 12 * w ^ 6 - 4480
    * σ ^ 12 * w ^ 4 * ω ^ 2 - 768 * σ ^ 12 * w ^ 2 * ω ^ 4 + 3136 * σ ^ 12 * ω ^ 6 + 11584 * σ ^ 10
    * w ^ 8 - 896 * σ ^ 10 * w ^ 6 * ω ^ 2 - 21120 * σ ^ 10 * w ^ 4 * ω ^ 4 + 23744 * σ ^ 10 * w ^ 2
    * ω ^ 6 - 7872 * σ ^ 10 * ω ^ 8 + 7808 * σ ^ 8 * w ^ 10 - 10688 * σ ^ 8 * w ^ 8 * ω ^ 2 + 4352 *
    σ ^ 8 * w ^ 6 * ω ^ 4 - 4672 * σ ^ 8 * w ^ 4 * ω ^ 6 + 7296 * σ ^ 8 * w ^ 2 * ω ^ 8 - 2880 *
    σ ^ 8 * ω ^ 10 + 2496 * σ ^ 6 * w ^ 12 - 7616 * σ ^ 6 * w ^ 10 * ω ^ 2 + 14144 * σ ^ 6 * w ^ 8 *
    ω ^ 4 - 19136 * σ ^ 6 * w ^ 6 * ω ^ 6 + 17984 * σ ^ 6 * w ^ 4 * ω ^ 8 - 9792 * σ ^ 6 * w ^ 2 *
    ω ^ 10 + 2240 * σ ^ 6 * ω ^ 12) * h

/-- **The current-carrying Bautin form extends the zero-current one**:
`bautinFormQ d σ ω₀ 0 = bautinForm d σ ω₀`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinFormQ_zero (d σ w : ℝ) :
    bautinFormQ d σ w 0 = bautinForm d σ w := by
  unfold bautinFormQ bautinForm
  ring


/-! ## The first Lyapunov coefficient (the instance `V = E` of the slice `δ* = 0`) -/

@[tmio M, powerlib_domain] private theorem zeroCurrent_Q_div (E R L w M D : ℝ) :
    (angleZero E E R L w M D).Q / M = 0 := by
  rw [← zeroCurrent_eq_angleZero, zeroCurrent_Q, zero_div]

/-- The positivity of the quartic coefficients of a physical zero-current boundary model. -/
@[tmio M, powerlib_domain] private theorem zeroCurrent_coeffs_pos {E R L w M D : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical) (hR : 0 < R) :
    0 < (zeroCurrent E R L w M D).g.coeff3 ∧
      0 < (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ∧
      0 < (zeroCurrent E R L w M D).g.coeff0 (zeroCurrent E R L w M D).Q := by
  obtain ⟨hN, hM', hD'⟩ := hp
  have hE : 0 < E := hN.E
  have hL : 0 < L := hN.L
  have hw : 0 < w := hN.ω0
  have hM : 0 < M := hM'
  have hD : 0 < D := hD'
  obtain ⟨h3, -, h1, h0⟩ := zeroCurrent_coeffs (E := E) (R := R) (w := w) (M := M) (D := D)
    hL.ne'
  rw [h3, h1, h0]
  exact ⟨by positivity, by positivity, by positivity⟩

/-- **`ℓ₁` = (explicit positive factor) · (−𝔅(model parameters))** on the zero-current boundary:
`ℓ₁ = −4 a² d σ ω 𝔅(d, σ, ω₀) / ((2σ + d)⁴ |r(iω)|² |r(2iω)|²)` at the critical pair
(`angleZeroQ`, `angleZeroP`) with `κ = 0` — the instance `V = E` of `angleZero_firstLyapunov`
(`bautinFormQ_zero`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_firstLyapunov_eq_bautinForm {E R L w M D ω : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q /
      (zeroCurrent E R L w M D).g.coeff3) :
    firstLyapunov (zeroCurrent E R L w M D).field 0 ω (angleZeroQ (E / M) (D / M) 0 (R / L) w ω)
        (angleZeroP (E / M) (D / M) 0 (R / L) w ω) =
      -(4 * (E / M) ^ 2 * (D / M) * (R / L) * ω /
          ((2 * (R / L) + D / M) ^ 4 * angleZeroR1 (D / M) (R / L) w 0 ω * angleZeroR2 (D / M) (R /
              L) w 0 ω)) * bautinForm (D / M) (R / L) w := by
  obtain ⟨-, -, h0⟩ := zeroCurrent_coeffs_pos hp (zeroCurrent_R_pos hp hH)
  rw [zeroCurrent_eq_angleZero] at hp hH hω2 h0 ⊢
  have h := angleZero_firstLyapunov hp hH h0 hω hω2
  rwa [zeroCurrent_Q_div, bautinFormQ_zero] at h

/-- **The first Lyapunov coefficient of the zero-current boundary in the frequency-normalised
form**: `ℓ₁ = a² d⁴ N(ω², σ², ω₀²) / (16 σ³ ω⁵ |r(iω)|² |r(2iω)|²)` (from
`zeroCurrent_firstLyapunov_eq_bautinForm`, `ellNum_mul_eq` and `ω²(2σ + d) = dρ`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_firstLyapunov {E R L w M D ω : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q /
      (zeroCurrent E R L w M D).g.coeff3) :
    firstLyapunov (zeroCurrent E R L w M D).field 0 ω (angleZeroQ (E / M) (D / M) 0 (R / L) w ω)
        (angleZeroP (E / M) (D / M) 0 (R / L) w ω) =
      (E / M) ^ 2 * (D / M) ^ 4 * ellNum (ω ^ 2) ((R / L) ^ 2) (w ^ 2) /
        (16 * (R / L) ^ 3 * ω ^ 5 * angleZeroR1 (D / M) (R / L) w 0 ω * angleZeroR2 (D / M) (R / L)
            w 0 ω) := by
  rw [zeroCurrent_firstLyapunov_eq_bautinForm hp hH hω hω2, eq_comm]
  have hR := zeroCurrent_R_pos hp hH
  have hf1 : D / M * ((R / L) ^ 2 + w ^ 2 - ω ^ 2) = 2 * (R / L) * ω ^ 2 := by
    have h := (angleZero_freq_relations (by rwa [zeroCurrent_eq_angleZero] at hp)
      (by rwa [zeroCurrent_eq_angleZero] at hH) (by rwa [zeroCurrent_eq_angleZero] at hω2)).1
    rw [zeroCurrent_Q_div, zero_add] at h
    exact h
  obtain ⟨hN, hM', hD'⟩ := hp
  have hL : 0 < L := hN.L
  have hM : 0 < M := hM'
  have hD : 0 < D := hD'
  have hα : 0 < 2 * (R / L) + D / M := by positivity
  have hK1 : 0 < angleZeroR1 (D / M) (R / L) w 0 ω := by unfold angleZeroR1; positivity
  have hK2 : 0 < angleZeroR2 (D / M) (R / L) w 0 ω := by unfold angleZeroR2; positivity
  have hρ : (D / M * ((R / L) ^ 2 + w ^ 2)) ^ 3 = (ω ^ 2 * (2 * (R / L) + D / M)) ^ 3 := by
    congr 1
    linear_combination hf1
  have hNe := ellNum_mul_eq hf1
  rw [show ∀ x y z : ℝ, -(x / y) * z = -(x * z) / y by intros; ring,
    div_eq_div_iff (by positivity) (by positivity)]
  apply mul_left_cancel₀ (pow_ne_zero 3 hα.ne')
  linear_combination ((E / M) ^ 2 * (D / M) ^ 4 * angleZeroR1 (D / M) (R / L) w 0 ω *
      angleZeroR2 (D / M) (R / L) w 0 ω) * hNe -
    (64 * (E / M) ^ 2 * (D / M) * (R / L) ^ 4 * bautinForm (D / M) (R / L) w *
      angleZeroR1 (D / M) (R / L) w 0 ω * angleZeroR2 (D / M) (R / L) w 0 ω) * hρ

/-- **The symbolic boundary between sub- and supercritical Hopf points**: for every critical pair
of a physical zero-current model on the Hopf boundary, `sign ℓ₁ = −sign 𝔅(D/M, R/L, ω₀)` (the
instance `V = E` of `angleZero_sign_firstLyapunov`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_sign_firstLyapunov {E R L w M D ω : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q)
    {q p : Fin 4 → ℂ} (hcp : IsCriticalPair (zeroCurrent E R L w M D).field 0 ω q p) :
    SignType.sign (firstLyapunov (zeroCurrent E R L w M D).field 0 ω q p) =
      -SignType.sign (bautinForm (D / M) (R / L) w) := by
  obtain ⟨-, h1, h0⟩ := zeroCurrent_coeffs_pos hp (zeroCurrent_R_pos hp hH)
  rw [zeroCurrent_eq_angleZero] at hp hH h1 h0 hcp ⊢
  have h := angleZero_sign_firstLyapunov hp hH h1 h0 hcp
  rwa [zeroCurrent_Q_div, bautinFormQ_zero] at h

/-! ## Connection conclusions -/

/-- **Supercritical zero-current Hopf points**: every physical zero-current model on the Hopf
boundary with `𝔅(D/M, R/L, ω₀) > 0` is locally asymptotically stable (the instance `V = E` of
`angleZero_mem_den_locallyAsymptoticallyStable`). -/
@[tmio TM, powerlib_domain] theorem zeroCurrent_mem_den_locallyAsymptoticallyStable
    {E R L w M D : ℝ} (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q)
    (hB : 0 < bautinForm (D / M) (R / L) w) :
    connection% (zeroCurrent E R L w M D ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨-, h1, h0⟩ := zeroCurrent_coeffs_pos hp (zeroCurrent_R_pos hp hH)
  rw [zeroCurrent_eq_angleZero] at hp hH h1 h0 ⊢
  exact angleZero_mem_den_locallyAsymptoticallyStable hp hH h1 h0
    (by rwa [zeroCurrent_Q_div, bautinFormQ_zero])

/-- **Subcritical zero-current Hopf points**: every physical zero-current model on the Hopf
boundary with `𝔅(D/M, R/L, ω₀) < 0` is unstable (the instance `V = E` of
`angleZero_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem zeroCurrent_mem_den_unstable {E R L w M D : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q)
    (hB : bautinForm (D / M) (R / L) w < 0) :
    connection% (zeroCurrent E R L w M D ∈ family.den (.flow .unstable)) := by
  obtain ⟨-, h1, h0⟩ := zeroCurrent_coeffs_pos hp (zeroCurrent_R_pos hp hH)
  rw [zeroCurrent_eq_angleZero] at hp hH h1 h0 ⊢
  exact angleZero_mem_den_unstable hp hH h1 h0 (by rwa [zeroCurrent_Q_div, bautinFormQ_zero])

/-! ## The Bautin set `{𝔅 = 0}`

`𝔅` is homogeneous of degree 11 in `(d, σ, ω₀)` (`bautinForm_homogeneous`) and even in `ω₀`: in
the ratios `x = d/σ` and `y = (ω₀/σ)² = (X/R)²` (`X = ω₀ L`) it is `σ¹¹ p(x, y)` with `p` quartic
in `y` (`bautinForm_eq_coeffs`, `bautinPolyY`): the coefficient of `y⁴` is `9x³ + 5x² + 4x − 10`
(`bautinHigh`, one positive root `x₄ ∈ (3/4, 4/5)`), those of `y²` and `y` are positive
(`bautinMid_pos`), the constant one is `(x + 1)² (5x⁴ + 14x³ − 17x² − 16x − 2)` (`bautinLow`, one
positive root `x₀ ∈ (7/5, 71/50)`). The Bautin set is exactly two graphs over the ratio `x`
(`bautinSet_eq_pair`, `bautinSet_eq_singleton`, `bautinSet_eq_empty`): a lower branch
`y_low(x) ∈ (0, 1)` for `x < x₀` and an upper branch `y_high(x) > 1` for `x < x₄`; they never meet
(the line `X = R`, `y = 1`, separates them, `bautinForm_self_pos`). Supercritical (`𝔅 > 0`)
exactly between them. -/

/-- The constant coefficient factor `5d⁴ + 14d³σ − 17d²σ² − 16dσ³ − 2σ⁴` of the Bautin form. -/
def bautinLow (d σ : ℝ) : ℝ := 5 * d ^ 4 + 14 * d ^ 3 * σ - 17 * d ^ 2 * σ ^ 2 - 16 * d * σ ^ 3 - 2
    * σ ^ 4

/-- The leading coefficient `9d³ + 5d²σ + 4dσ² − 10σ³` of the Bautin form in `ω₀⁸`. -/
def bautinHigh (d σ : ℝ) : ℝ := 9 * d ^ 3 + 5 * d ^ 2 * σ + 4 * d * σ ^ 2 - 10 * σ ^ 3

/-- The Bautin form as a quartic in `ω₀²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_eq_coeffs (d σ w : ℝ) :
    bautinForm d σ w = bautinHigh d σ * w ^ 8 +
      (4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 + 16 * d * σ ^ 4 -
        8 * σ ^ 5) * w ^ 6 +
      (d ^ 7 + 9 * d ^ 6 * σ + 36 * d ^ 5 * σ ^ 2 + 76 * d ^ 4 * σ ^ 3 + 215 * d ^ 3 * σ ^ 4 +
        242 * d ^ 2 * σ ^ 5 + 96 * d * σ ^ 6 + 12 * σ ^ 7) * w ^ 4 +
      σ ^ 2 * (d + σ) * (d ^ 6 + 11 * d ^ 5 * σ + 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 +
        42 * d ^ 2 * σ ^ 4 + 56 * d * σ ^ 5 + 8 * σ ^ 6) * w ^ 2 +
      σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ := by
  unfold bautinForm bautinHigh bautinLow
  ring

/-- **The line `X = R` is supercritical**: `𝔅(d, σ, σ) = 2dσ⁴(d⁶ + 13d⁵σ + 52d⁴σ² + 68d³σ³ +
156d²σ⁴ + 180dσ⁵ + 80σ⁶) > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_self_pos {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ) :
    0 < bautinForm d σ σ := by
  have h : bautinForm d σ σ = 2 * d * σ ^ 4 * (d ^ 6 + 13 * d ^ 5 * σ + 52 * d ^ 4 * σ ^ 2 +
      68 * d ^ 3 * σ ^ 3 + 156 * d ^ 2 * σ ^ 4 + 180 * d * σ ^ 5 + 80 * σ ^ 6) := by
    unfold bautinForm
    ring
  rw [h]
  positivity

/-- `bautinLow < 0` for `0 < d ≤ 7σ/5`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinLow_neg {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (h : d ≤ 7 / 5 * σ) : bautinLow d σ < 0 := by
  unfold bautinLow
  have h0 : 0 ≤ 7 / 5 * σ - d := by linarith
  nlinarith [mul_nonneg h0 (pow_nonneg hd.le 3), mul_nonneg h0 (mul_nonneg (pow_nonneg hd.le 2)
    hσ.le), mul_nonneg h0 (mul_nonneg hd.le (pow_nonneg hσ.le 2)), mul_nonneg h0 (pow_nonneg hσ.le
        3),
    mul_pos hd hσ, pow_pos hσ 4, pow_pos hd 2]

/-- `bautinLow > 0` for `d ≥ 71σ/50`: the threshold `x₀` lies in `(7/5, 71/50)`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem bautinLow_pos {d σ : ℝ} (hσ : 0 < σ) (h : 71 / 50 * σ ≤ d) :
    0 < bautinLow d σ := by
  unfold bautinLow
  have h0 : 0 ≤ d - 71 / 50 * σ := by linarith
  have hd : 0 < d := by linarith
  nlinarith [mul_nonneg h0 (pow_nonneg hd.le 3), mul_nonneg h0 (mul_nonneg (pow_nonneg hd.le 2)
    hσ.le), mul_nonneg h0 (mul_nonneg hd.le (pow_nonneg hσ.le 2)), mul_nonneg h0 (pow_nonneg hσ.le
        3),
    mul_pos hd hσ, pow_pos hσ 4, pow_pos hd 2]

/-- `bautinHigh < 0` for `0 < d ≤ 3σ/4` and `> 0` for `d ≥ 4σ/5`: the threshold `x₄` lies in
`(3/4, 4/5)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinHigh_neg {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (h : d ≤ 3 / 4 * σ) : bautinHigh d σ < 0 := by
  unfold bautinHigh
  have h0 : 0 ≤ 3 / 4 * σ - d := by linarith
  nlinarith [mul_nonneg h0 (pow_nonneg hd.le 2), mul_nonneg h0 (mul_nonneg hd.le hσ.le),
    mul_nonneg h0 (pow_nonneg hσ.le 2), pow_pos hσ 3]

@[tmio M, powerlib_domain] theorem bautinHigh_pos {d σ : ℝ} (hσ : 0 < σ) (h : 4 / 5 * σ ≤ d) :
    0 < bautinHigh d σ := by
  unfold bautinHigh
  have h0 : 0 ≤ d - 4 / 5 * σ := by linarith
  have hd : 0 < d := by linarith
  nlinarith [mul_nonneg h0 (pow_nonneg hd.le 2), mul_nonneg h0 (mul_nonneg hd.le hσ.le),
    mul_nonneg h0 (pow_nonneg hσ.le 2), pow_pos hσ 3]

/-- `bautinLow ≥ 0` forces `d > 7σ/5`, hence `bautinHigh > 0`. -/
@[tmio M, powerlib_domain] private theorem bautinHigh_pos_of_bautinLow {d σ : ℝ} (hd : 0 < d)
    (hσ : 0 < σ) (h : 0 ≤ bautinLow d σ) : 7 / 5 * σ < d ∧ 0 < bautinHigh d σ := by
  have h75 : 7 / 5 * σ < d := by
    by_contra hc
    exact absurd h (not_le.mpr (bautinLow_neg hd hσ (not_lt.mp hc)))
  exact ⟨h75, bautinHigh_pos hσ (by linarith)⟩

/-- The coefficients of `ω₀⁴` and `ω₀²` are positive (`29x² − 5x + 42 > 0`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bautinMid_pos {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ) :
    0 < d ^ 7 + 9 * d ^ 6 * σ + 36 * d ^ 5 * σ ^ 2 + 76 * d ^ 4 * σ ^ 3 + 215 * d ^ 3 * σ ^ 4 +
        242 * d ^ 2 * σ ^ 5 + 96 * d * σ ^ 6 + 12 * σ ^ 7 ∧
      0 < σ ^ 2 * (d + σ) * (d ^ 6 + 11 * d ^ 5 * σ + 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 +
        42 * d ^ 2 * σ ^ 4 + 56 * d * σ ^ 5 + 8 * σ ^ 6) := by
  refine ⟨by positivity, ?_⟩
  have hq : 0 < 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 + 42 * d ^ 2 * σ ^ 4 := by
    have : 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 + 42 * d ^ 2 * σ ^ 4 =
        d ^ 2 * σ ^ 2 * (29 * (d - 5 / 58 * σ) ^ 2 + 4847 / 116 * σ ^ 2) := by ring
    rw [this]
    positivity
  have : 0 < d ^ 6 + 11 * d ^ 5 * σ + 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 +
      42 * d ^ 2 * σ ^ 4 + 56 * d * σ ^ 5 + 8 * σ ^ 6 := by
    have h6 : 0 < d ^ 6 + 11 * d ^ 5 * σ + 56 * d * σ ^ 5 + 8 * σ ^ 6 := by positivity
    linarith
  positivity

/-- **Supercritical for every grid frequency when `bautinLow ≥ 0`**: then `𝔅(d, σ, ω₀) > 0` for
every `ω₀ > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_pos_of_bautinLow {d σ w : ℝ} (hd : 0 < d)
    (hσ : 0 < σ) (hw : 0 < w) (h : 0 ≤ bautinLow d σ) : 0 < bautinForm d σ w := by
  obtain ⟨h75, h4⟩ := bautinHigh_pos_of_bautinLow hd hσ h
  obtain ⟨h2, h1⟩ := bautinMid_pos hd hσ
  have h3 : 0 < 4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 +
      16 * d * σ ^ 4 - 8 * σ ^ 5 := by
    have : 8 * σ ^ 5 < 16 * d * σ ^ 4 := by
      have := mul_lt_mul_of_pos_right h75 (pow_pos hσ 4)
      nlinarith [pow_pos hσ 5]
    have : 0 ≤ 4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 := by
      positivity
    linarith
  rw [bautinForm_eq_coeffs]
  have := mul_pos h4 (pow_pos hw 8)
  have := mul_pos h3 (pow_pos hw 6)
  have := mul_pos h2 (pow_pos hw 4)
  have := mul_pos h1 (pow_pos hw 2)
  have : 0 ≤ σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ := by positivity
  linarith

/-- **Subcritical points at small `X/R` when `bautinLow < 0`**: then `𝔅(d, σ, ω₀) < 0` for some
`ω₀ > 0` (`𝔅(d, σ, 0) = σ⁵(d + σ)² bautinLow(d, σ)`, continuity). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_bautinForm_neg {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (h : bautinLow d σ < 0) : ∃ w > 0, bautinForm d σ w < 0 := by
  have h0 : bautinForm d σ 0 < 0 := by
    rw [bautinForm_eq_coeffs]
    have : σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ < 0 :=
      mul_neg_of_pos_of_neg (by positivity) h
    simpa using this
  have hc : Continuous fun w => bautinForm d σ w := by
    unfold bautinForm
    fun_prop
  have hev : ∀ᶠ w in nhdsWithin (0 : ℝ) (Set.Ioi 0), bautinForm d σ w < 0 :=
    eventually_nhdsWithin_of_eventually_nhds (hc.continuousAt.eventually_lt continuousAt_const h0)
  obtain ⟨w, hw, hw0⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨w, hw0, hw⟩

/-- **The exact supercritical threshold of the damping ratio**: `𝔅(d, σ, ω₀) > 0` for every
`ω₀ > 0` iff `bautinLow(d, σ) ≥ 0`, i.e. iff `d ≥ x₀ σ`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem forall_bautinForm_pos_iff {d σ : ℝ} (hd : 0 < d)
    (hσ : 0 < σ) : (∀ w > 0, 0 < bautinForm d σ w) ↔ 0 ≤ bautinLow d σ := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨w, hw, hneg⟩ := exists_bautinForm_neg hd hσ (not_le.mp hc)
    exact absurd (h w hw) (not_lt.mpr hneg.le)
  · exact fun h w hw => bautinForm_pos_of_bautinLow hd hσ hw h

/-- **No Bautin point with `X ≥ R` when `bautinHigh ≥ 0`**: if `bautinHigh(d, σ) ≥ 0` then
`𝔅(d, σ, ω₀) > 0` for every `ω₀ ≥ σ` (every coefficient but the constant one is then non-negative,
so `𝔅(d, σ, ω₀) ≥ 𝔅(d, σ, σ) > 0` term by term). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_pos_of_one_le {d σ w : ℝ} (hd : 0 < d)
    (hσ : 0 < σ) (hw : σ ≤ w) (h : 0 ≤ bautinHigh d σ) : 0 < bautinForm d σ w := by
  have h34 : 3 / 4 * σ < d := by
    by_contra hc
    exact absurd h (not_le.mpr (bautinHigh_neg hd hσ (not_lt.mp hc)))
  obtain ⟨h2, h1⟩ := bautinMid_pos hd hσ
  have h3 : 0 < 4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 +
      16 * d * σ ^ 4 - 8 * σ ^ 5 := by
    have : 12 * σ ^ 5 < 16 * d * σ ^ 4 := by
      have := mul_lt_mul_of_pos_right h34 (pow_pos hσ 4)
      nlinarith [pow_pos hσ 5]
    have : 0 ≤ 4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 := by
      positivity
    nlinarith [pow_pos hσ 5]
  have hself := bautinForm_self_pos hd hσ
  rw [bautinForm_eq_coeffs] at hself ⊢
  have e8 : σ ^ 8 ≤ w ^ 8 := pow_le_pow_left₀ hσ.le hw 8
  have e6 : σ ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ hσ.le hw 6
  have e4 : σ ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ hσ.le hw 4
  have e2 : σ ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hσ.le hw 2
  nlinarith [mul_le_mul_of_nonneg_left e8 h, mul_le_mul_of_nonneg_left e6 h3.le,
    mul_le_mul_of_nonneg_left e4 h2.le, mul_le_mul_of_nonneg_left e2 h1.le]

/-! ## The Bautin set: exactly two branches -/

section BautinBranches
open Polynomial Filter Topology Set

/-- **The Bautin form as a quartic in `y = ω₀²`** (the coefficients of `bautinForm_eq_coeffs`). -/
def bautinPolyY (d σ : ℝ) : ℝ[X] :=
  C (bautinHigh d σ) * X ^ 4 +
    C (4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 + 16 * d * σ ^ 4 -
      8 * σ ^ 5) * X ^ 3 +
    C (d ^ 7 + 9 * d ^ 6 * σ + 36 * d ^ 5 * σ ^ 2 + 76 * d ^ 4 * σ ^ 3 + 215 * d ^ 3 * σ ^ 4 +
      242 * d ^ 2 * σ ^ 5 + 96 * d * σ ^ 6 + 12 * σ ^ 7) * X ^ 2 +
    C (σ ^ 2 * (d + σ) * (d ^ 6 + 11 * d ^ 5 * σ + 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 +
      42 * d ^ 2 * σ ^ 4 + 56 * d * σ ^ 5 + 8 * σ ^ 6)) * X +
    C (σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ)

/-- `bautinPolyY` evaluated at `ω₀²` is the Bautin form. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPolyY_eval_sq (d σ w : ℝ) :
    (bautinPolyY d σ).eval (w ^ 2) = bautinForm d σ w := by
  rw [bautinForm_eq_coeffs]
  simp only [bautinPolyY, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

@[tmio M, powerlib_domain] private theorem bautinPolyY_degree {d σ : ℝ} (h : bautinHigh d σ ≠ 0) :
    (bautinPolyY d σ).degree = 4 := by
  unfold bautinPolyY
  compute_degree!

/-- **Descartes' rule of signs for the Bautin quartic**: if `bautinHigh d σ < 0` (then also
`bautinLow d σ < 0`) the coefficient signs are `(−, ±, +, +, −)`, two sign variations, so the
quartic has at most two positive roots counted with multiplicity
(`Polynomial.roots_countP_pos_le_signVariations`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPolyY_countP_pos_le {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (hH : bautinHigh d σ < 0) : (bautinPolyY d σ).roots.countP (0 < ·) ≤ 2 := by
  have h45 : d < 4 / 5 * σ := by
    by_contra hc
    exact absurd hH (not_lt.mpr (bautinHigh_pos hσ (not_lt.mp hc)).le)
  have hL : bautinLow d σ < 0 := bautinLow_neg hd hσ (by linarith)
  obtain ⟨h2, h1⟩ := bautinMid_pos hd hσ
  have h0 : σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ < 0 := mul_neg_of_pos_of_neg (by positivity) hL
  refine (roots_countP_pos_le_signVariations _).trans (le_of_eq ?_)
  have hl : (bautinPolyY d σ).coeffList = [bautinHigh d σ,
      4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 + 16 * d * σ ^ 4 -
        8 * σ ^ 5,
      d ^ 7 + 9 * d ^ 6 * σ + 36 * d ^ 5 * σ ^ 2 + 76 * d ^ 4 * σ ^ 3 + 215 * d ^ 3 * σ ^ 4 +
        242 * d ^ 2 * σ ^ 5 + 96 * d * σ ^ 6 + 12 * σ ^ 7,
      σ ^ 2 * (d + σ) * (d ^ 6 + 11 * d ^ 5 * σ + 29 * d ^ 4 * σ ^ 2 - 5 * d ^ 3 * σ ^ 3 +
        42 * d ^ 2 * σ ^ 4 + 56 * d * σ ^ 5 + 8 * σ ^ 6),
      σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ] := by
    have key : ∀ c₄ c₃ c₂ c₁ c₀ : ℝ, c₄ ≠ 0 →
        (C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀).coeffList =
          [c₄, c₃, c₂, c₁, c₀] := by
      intro c₄ c₃ c₂ c₁ c₀ h₄
      have hdeg : (C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀).degree = 4 := by
        compute_degree!
      rw [coeffList, hdeg]
      simp [List.range_succ, coeff_X, coeff_C, coeff_X_pow]
    exact key _ _ _ _ _ hH.ne
  rw [signVariations, hl]
  rcases lt_trichotomy (4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 +
      16 * d * σ ^ 4 - 8 * σ ^ 5) 0 with h3 | h3 | h3
  · rw [List.signVariations_congr (l₂ := [(-1 : ℤ), -1, 1, 1, -1])]
    · decide
    · simp [sign_neg hH, sign_neg h3, sign_pos h2, sign_pos h1, sign_neg h0]
  · rw [List.signVariations_congr (l₂ := [(-1 : ℤ), 0, 1, 1, -1])]
    · decide
    · simp [sign_neg hH, h3, sign_pos h2, sign_pos h1, sign_neg h0]
  · rw [List.signVariations_congr (l₂ := [(-1 : ℤ), 1, 1, 1, -1])]
    · decide
    · simp [sign_neg hH, sign_pos h3, sign_pos h2, sign_pos h1, sign_neg h0]

/-- At most two positive zeros: three distinct positive roots contradict Descartes' bound. -/
@[tmio M, powerlib_domain] private theorem bautinPolyY_no_three {d σ : ℝ} (hd : 0 < d)
    (hσ : 0 < σ) (hH : bautinHigh d σ < 0) {y₁ y₂ y₃ : ℝ} (h₁ : 0 < y₁) (h₂ : 0 < y₂)
    (h₃ : 0 < y₃) (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃)
    (e₁ : (bautinPolyY d σ).eval y₁ = 0) (e₂ : (bautinPolyY d σ).eval y₂ = 0) :
    (bautinPolyY d σ).eval y₃ ≠ 0 := by
  intro e₃
  have hP : bautinPolyY d σ ≠ 0 := by
    intro h
    have := bautinPolyY_degree hH.ne
    rw [h, degree_zero] at this
    exact absurd this (by decide)
  have hsub : ({y₁, y₂, y₃} : Multiset ℝ) ≤ (bautinPolyY d σ).roots := by
    rw [Multiset.le_iff_subset (by simp [h12, h13, h23])]
    intro y hy
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hy
    rw [mem_roots hP, IsRoot.def]
    rcases hy with rfl | rfl | rfl <;> assumption
  have hc := (Multiset.countP_le_of_le (fun y : ℝ => 0 < y) hsub).trans
    (bautinPolyY_countP_pos_le hd hσ hH)
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.countP_cons_of_pos _ h₁,
    Multiset.countP_cons_of_pos _ h₂, ← Multiset.cons_zero, Multiset.countP_cons_of_pos _ h₃] at hc
  simp at hc

@[tmio M, powerlib_domain] private theorem bautinPolyY_eval_zero (d σ : ℝ) :
    (bautinPolyY d σ).eval 0 = σ ^ 5 * (d + σ) ^ 2 * bautinLow d σ := by
  simp [bautinPolyY]

@[tmio M, powerlib_domain] private theorem bautinPolyY_coeff_four (d σ : ℝ) :
    (bautinPolyY d σ).coeff 4 = bautinHigh d σ := by
  simp only [bautinPolyY, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- No zero on `[a, b]` keeps a positive sign (intermediate values). -/
@[tmio M, powerlib_domain] private theorem bautinPolyY_pos_of_no_root {d σ a b : ℝ}
    (hroot : ∀ y ∈ uIcc a b, (bautinPolyY d σ).eval y ≠ 0) (ha : 0 < (bautinPolyY d σ).eval a) :
    0 < (bautinPolyY d σ).eval b := by
  by_contra hb
  push Not at hb
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (f := fun y => (bautinPolyY d σ).eval y)
    (Polynomial.continuous _).continuousOn (Set.mem_uIcc.mpr (Or.inr ⟨hb, ha.le⟩))
  exact hroot c hc hc0

/-- No zero on `[a, b]` keeps a negative sign (intermediate values). -/
@[tmio M, powerlib_domain] private theorem bautinPolyY_neg_of_no_root {d σ a b : ℝ}
    (hroot : ∀ y ∈ uIcc a b, (bautinPolyY d σ).eval y ≠ 0) (ha : (bautinPolyY d σ).eval a < 0) :
    (bautinPolyY d σ).eval b < 0 := by
  by_contra hb
  push Not at hb
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (f := fun y => (bautinPolyY d σ).eval y)
    (Polynomial.continuous _).continuousOn (Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb⟩))
  exact hroot c hc hc0

/-- The coefficient of `ω₀⁶` is positive once `bautinHigh ≥ 0` (`d > 3σ/4`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem bautinC3_pos_of_bautinHigh {d σ : ℝ} (hd : 0 < d)
    (hσ : 0 < σ) (h : 0 ≤ bautinHigh d σ) :
    0 < 4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 + 16 * d * σ ^ 4 -
      8 * σ ^ 5 := by
  have h34 : 3 / 4 * σ < d := by
    by_contra hc
    exact absurd h (not_le.mpr (bautinHigh_neg hd hσ (not_lt.mp hc)))
  have : 12 * σ ^ 5 < 16 * d * σ ^ 4 := by
    have := mul_lt_mul_of_pos_right h34 (pow_pos hσ 4)
    nlinarith [pow_pos hσ 5]
  have : 0 ≤ 4 * d ^ 5 + 20 * d ^ 4 * σ + 87 * d ^ 3 * σ ^ 2 + 66 * d ^ 2 * σ ^ 3 := by
    positivity
  nlinarith [pow_pos hσ 5]

/-- The Bautin form is homogeneous of degree 11: `𝔅(td, tσ, tω₀) = t¹¹ 𝔅(d, σ, ω₀)`, so its zero set
is a cone over its trace at `σ = 1` (the ratios `x = d/σ`, `y = (ω₀/σ)²`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bautinForm_homogeneous (t d σ w : ℝ) :
    bautinForm (t * d) (t * σ) (t * w) = t ^ 11 * bautinForm d σ w := by
  unfold bautinForm
  ring

/-- **No Bautin point when `bautinLow ≥ 0`** (`d ≥ x₀ σ`): the zero set in `ω₀ > 0` is empty.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSet_eq_empty {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (hL : 0 ≤ bautinLow d σ) : {w : ℝ | 0 < w ∧ bautinForm d σ w = 0} = ∅ := by
  ext w
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  exact fun hw => (bautinForm_pos_of_bautinLow hd hσ hw hL).ne'

/-- **One branch when `bautinLow < 0 ≤ bautinHigh`** (`x₄ σ ≤ d < x₀ σ`): the zero set in
`ω₀ > 0` is a single point `ω_low ∈ (0, σ)` (the quartic in `ω₀²` is strictly increasing), and
`𝔅 > 0` (supercritical) exactly for `ω₀ > ω_low`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSet_eq_singleton {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (hL : bautinLow d σ < 0) (hH : 0 ≤ bautinHigh d σ) :
    ∃ wl ∈ Ioo 0 σ, {w : ℝ | 0 < w ∧ bautinForm d σ w = 0} = {wl} ∧
      ∀ w, 0 < w → (0 < bautinForm d σ w ↔ wl < w) := by
  obtain ⟨h2, h1⟩ := bautinMid_pos hd hσ
  have h3 := bautinC3_pos_of_bautinHigh hd hσ hH
  set f := fun y => (bautinPolyY d σ).eval y with hf
  have hmono : StrictMonoOn f (Ici 0) := by
    intro y hy y' hy' hyy'
    have hy0 : (0 : ℝ) ≤ y := hy
    simp only [hf, bautinPolyY, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    have e4 : y ^ 4 ≤ y' ^ 4 := pow_le_pow_left₀ hy0 hyy'.le 4
    have e3 : y ^ 3 < y' ^ 3 := pow_lt_pow_left₀ hyy' hy0 (by norm_num)
    have e2 : y ^ 2 < y' ^ 2 := pow_lt_pow_left₀ hyy' hy0 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left e4 hH, mul_lt_mul_of_pos_left e3 h3,
      mul_lt_mul_of_pos_left e2 h2, mul_lt_mul_of_pos_left hyy' h1]
  have f0 : f 0 < 0 := by
    simp only [hf, bautinPolyY_eval_zero]
    exact mul_neg_of_pos_of_neg (by positivity) hL
  have fσ : 0 < f (σ ^ 2) := by
    simp only [hf, bautinPolyY_eval_sq]
    exact bautinForm_self_pos hd hσ
  obtain ⟨y₁, hy₁, e₁⟩ := intermediate_value_Ioo (sq_nonneg σ)
    (Polynomial.continuous (bautinPolyY d σ)).continuousOn (show (0 : ℝ) ∈ Ioo (f 0) (f (σ ^ 2))
      from ⟨f0, fσ⟩)
  change f y₁ = 0 at e₁
  have hy₁0 : 0 < y₁ := hy₁.1
  have huniq : ∀ y, 0 ≤ y → (f y = 0 ↔ y = y₁) := by
    intro y hy
    constructor
    · intro h
      exact hmono.injOn hy (mem_Ici.mpr hy₁0.le) (h.trans e₁.symm)
    · rintro rfl
      exact e₁
  refine ⟨Real.sqrt y₁, ⟨Real.sqrt_pos.mpr hy₁0, ?_⟩, ?_, ?_⟩
  · rw [Real.sqrt_lt' hσ]
    exact hy₁.2
  · ext w
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hw, h0⟩
      have : w ^ 2 = y₁ := (huniq (w ^ 2) (sq_nonneg w)).mp (by simpa [hf, bautinPolyY_eval_sq])
      rw [← this, Real.sqrt_sq hw.le]
    · rintro rfl
      refine ⟨Real.sqrt_pos.mpr hy₁0, ?_⟩
      rw [← bautinPolyY_eval_sq, Real.sq_sqrt hy₁0.le]
      exact e₁
  · intro w hw
    rw [← bautinPolyY_eval_sq, Real.sqrt_lt' hw]
    change 0 < f (w ^ 2) ↔ y₁ < w ^ 2
    constructor
    · intro hpos
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hlt | heq
      · exact absurd (hmono (mem_Ici.mpr (sq_nonneg w)) (mem_Ici.mpr hy₁0.le) hlt)
          (by rw [e₁]; exact not_lt.mpr hpos.le)
      · rw [heq] at hpos
        exact absurd e₁ hpos.ne'
    · intro hlt
      have := hmono (mem_Ici.mpr hy₁0.le) (mem_Ici.mpr (sq_nonneg w)) hlt
      rwa [e₁] at this

/-- **Two branches when `bautinHigh < 0`** (`d < x₄ σ`): the zero set in `ω₀ > 0` is exactly two
points `ω_low ∈ (0, σ)` and `ω_high ∈ (σ, ∞)` (Descartes' rule bounds the positive roots of the
quartic in `ω₀²` by two, intermediate values give one on each side of `ω₀ = σ`), and `𝔅 > 0`
(supercritical) exactly for `ω_low < ω₀ < ω_high`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSet_eq_pair {d σ : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (hH : bautinHigh d σ < 0) :
    ∃ wl ∈ Ioo 0 σ, ∃ wh ∈ Ioi σ, {w : ℝ | 0 < w ∧ bautinForm d σ w = 0} = {wl, wh} ∧
      ∀ w, 0 < w → (0 < bautinForm d σ w ↔ wl < w ∧ w < wh) := by
  have h45 : d < 4 / 5 * σ := by
    by_contra hc
    exact absurd hH (not_lt.mpr (bautinHigh_pos hσ (not_lt.mp hc)).le)
  have hL : bautinLow d σ < 0 := bautinLow_neg hd hσ (by linarith)
  set f := fun y => (bautinPolyY d σ).eval y with hf
  have hcont : Continuous f := Polynomial.continuous _
  have f0 : f 0 < 0 := by
    simp only [hf, bautinPolyY_eval_zero]
    exact mul_neg_of_pos_of_neg (by positivity) hL
  have fσ : 0 < f (σ ^ 2) := by
    simp only [hf, bautinPolyY_eval_sq]
    exact bautinForm_self_pos hd hσ
  have hdeg := bautinPolyY_degree hH.ne
  have hlim : Tendsto f atTop atBot := by
    refine tendsto_atBot_of_leadingCoeff_nonpos (P := bautinPolyY d σ) (by rw [hdeg]; decide) ?_
    rw [leadingCoeff, natDegree_eq_of_degree_eq_some hdeg, bautinPolyY_coeff_four]
    exact hH.le
  have hev : ∀ x, ∃ Y > x, f Y < 0 := fun x =>
    ((hlim.eventually (eventually_lt_atBot 0)).and (eventually_gt_atTop x)).exists.imp
      fun Y h => ⟨h.2, h.1⟩
  obtain ⟨Y, hY, fY⟩ := hev (σ ^ 2)
  obtain ⟨y₁, hy₁, e₁⟩ := intermediate_value_Ioo (sq_nonneg σ) hcont.continuousOn
    (show (0 : ℝ) ∈ Ioo (f 0) (f (σ ^ 2)) from ⟨f0, fσ⟩)
  obtain ⟨y₂, hy₂, e₂⟩ := intermediate_value_Ioo' hY.le hcont.continuousOn
    (show (0 : ℝ) ∈ Ioo (f Y) (f (σ ^ 2)) from ⟨fY, fσ⟩)
  have hy₁0 : 0 < y₁ := hy₁.1
  have hy₂0 : 0 < y₂ := by linarith [hy₂.1, sq_nonneg σ]
  have h12 : y₁ < y₂ := hy₁.2.trans hy₂.1
  have hroots : ∀ y, 0 < y → f y = 0 → y = y₁ ∨ y = y₂ := by
    intro y hy hy0
    by_contra hne
    push Not at hne
    exact bautinPolyY_no_three hd hσ hH hy₁0 hy₂0 hy h12.ne hne.1.symm hne.2.symm e₁ e₂ hy0
  have f0ne : f 0 ≠ 0 := f0.ne
  -- no root in an interval of positive reals avoiding `y₁, y₂`
  have noroot : ∀ a b, (∀ c ∈ uIcc a b, c ≠ y₁ ∧ c ≠ y₂ ∧ 0 ≤ c) →
      ∀ c ∈ uIcc a b, f c ≠ 0 := by
    intro a b h c hc hc0
    obtain ⟨n1, n2, n0⟩ := h c hc
    rcases n0.lt_or_eq with hpos | hzero
    · rcases hroots c hpos hc0 with h' | h'
      · exact n1 h'
      · exact n2 h'
    · exact f0ne (hzero ▸ hc0)
  refine ⟨Real.sqrt y₁, ⟨Real.sqrt_pos.mpr hy₁0, ?_⟩, Real.sqrt y₂, ?_, ?_, ?_⟩
  · rw [Real.sqrt_lt' hσ]
    exact hy₁.2
  · show σ < Real.sqrt y₂
    rw [Real.lt_sqrt hσ.le]
    exact hy₂.1
  · ext w
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hw, h0⟩
      rcases hroots (w ^ 2) (by positivity) (by simpa [hf, bautinPolyY_eval_sq]) with h' | h'
      · left
        rw [← h', Real.sqrt_sq hw.le]
      · right
        rw [← h', Real.sqrt_sq hw.le]
    · rintro (rfl | rfl)
      · refine ⟨Real.sqrt_pos.mpr hy₁0, ?_⟩
        rw [← bautinPolyY_eval_sq, Real.sq_sqrt hy₁0.le]
        exact e₁
      · refine ⟨Real.sqrt_pos.mpr hy₂0, ?_⟩
        rw [← bautinPolyY_eval_sq, Real.sq_sqrt hy₂0.le]
        exact e₂
  · intro w hw
    rw [← bautinPolyY_eval_sq, Real.sqrt_lt' hw, Real.lt_sqrt hw.le]
    change 0 < f (w ^ 2) ↔ y₁ < w ^ 2 ∧ w ^ 2 < y₂
    have hw2 : 0 < w ^ 2 := by positivity
    constructor
    · intro hpos
      have hne1 : w ^ 2 ≠ y₁ := fun h => by rw [h] at hpos; exact hpos.ne' e₁
      have hne2 : w ^ 2 ≠ y₂ := fun h => by rw [h] at hpos; exact hpos.ne' e₂
      constructor
      · by_contra hle
        push Not at hle
        have hlt : w ^ 2 < y₁ := lt_of_le_of_ne hle hne1
        have := bautinPolyY_pos_of_no_root (a := w ^ 2) (b := 0)
          (noroot _ _ fun c hc => by
            rw [mem_uIcc] at hc
            rcases hc with ⟨_, h⟩ | ⟨h0, h⟩
            · exact ⟨by linarith, by linarith, by linarith⟩
            · exact ⟨by linarith, by linarith, h0⟩) hpos
        exact absurd f0 (not_lt.mpr this.le)
      · by_contra hle
        push Not at hle
        have hlt : y₂ < w ^ 2 := lt_of_le_of_ne hle (Ne.symm hne2)
        obtain ⟨Y', hY', fY'⟩ := hev (w ^ 2)
        have := bautinPolyY_pos_of_no_root (a := w ^ 2) (b := Y')
          (noroot _ _ fun c hc => by
            rw [mem_uIcc] at hc
            rcases hc with ⟨h, _⟩ | ⟨_, h⟩
            · exact ⟨by linarith, by linarith, by linarith⟩
            · exact ⟨by linarith, by linarith, by linarith⟩) hpos
        exact absurd fY' (not_lt.mpr this.le)
    · rintro ⟨h1, h2⟩
      by_contra hle
      push Not at hle
      have hne : f (w ^ 2) ≠ 0 := fun h0 => by
        rcases hroots (w ^ 2) hw2 h0 with h | h
        · exact h1.ne' h
        · exact h2.ne h
      have hneg : f (w ^ 2) < 0 := lt_of_le_of_ne hle hne
      have := bautinPolyY_neg_of_no_root (a := w ^ 2) (b := σ ^ 2)
        (noroot _ _ fun c hc => by
          rw [mem_uIcc] at hc
          have := hy₁.2
          have := hy₂.1
          rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact ⟨by linarith, by linarith, by linarith⟩
          · exact ⟨by linarith, by linarith, by linarith⟩) hneg
      exact absurd fσ (not_lt.mpr this.le)


end BautinBranches

/-! ## The explicit boundary family and its connection conclusions -/

/-- **The boundary point with damping ratio `d`**: `zeroCurrent E R L ω₀ M(d) (d M(d))`, `M(d) =
hopfInertia E R L ω₀ d`. -/
def zeroCurrentHopf (E R L w d : ℝ) : Model :=
  zeroCurrent E R L w (hopfInertia E R L w d) (d * hopfInertia E R L w d)

/-- The boundary family is physical and on the Hopf boundary, with damping ratio `D/M = d`, for
all `E, R, L, ω₀, d > 0`. Satisfaction of the requirements. -/
@[tmio M, powerlib_domain] theorem zeroCurrentHopf_meets {E R L w d : ℝ} (hE : 0 < E)
    (hR : 0 < R) (hL : 0 < L) (hw : 0 < w) (hd : 0 < d) :
    Meets (zeroCurrentHopf E R L w d) .physical ∧
      d * hopfInertia E R L w d / hopfInertia E R L w d = d ∧
      (zeroCurrentHopf E R L w d).g.coeff3 * (zeroCurrentHopf E R L w d).g.coeff2
          (zeroCurrentHopf E R L w d).Q * (zeroCurrentHopf E R L w d).g.coeff1
          (zeroCurrentHopf E R L w d).Q =
        (zeroCurrentHopf E R L w d).g.coeff1 (zeroCurrentHopf E R L w d).Q ^ 2 +
          (zeroCurrentHopf E R L w d).g.coeff3 ^ 2 * (zeroCurrentHopf E R L w d).g.coeff0
            (zeroCurrentHopf E R L w d).Q := by
  have hM : 0 < hopfInertia E R L w d := by
    unfold hopfInertia
    positivity
  have hdM : d * hopfInertia E R L w d / hopfInertia E R L w d = d := by
    field_simp
  refine ⟨⟨⟨hE, hE, hR.le, hL, hw⟩, hM, mul_pos hd hM⟩, hdM, ?_⟩
  unfold zeroCurrentHopf
  rw [zeroCurrent_hopf_iff_inertia hR hL hw hM (by positivity), hdM]

/-- **Supercritical boundary points of the family**: `zeroCurrentHopf E R L ω₀ d` is locally
asymptotically stable when `𝔅(d, R/L, ω₀) > 0` (`zeroCurrent_mem_den_locallyAsymptoticallyStable`).
-/
@[tmio TM, powerlib_domain] theorem zeroCurrentHopf_mem_den_locallyAsymptoticallyStable
    {E R L w d : ℝ} (hE : 0 < E) (hR : 0 < R) (hL : 0 < L) (hw : 0 < w) (hd : 0 < d)
    (hB : 0 < bautinForm d (R / L) w) :
    connection% (zeroCurrentHopf E R L w d ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨hp, hdM, hH⟩ := zeroCurrentHopf_meets hE hR hL hw hd
  unfold zeroCurrentHopf at hp hH ⊢
  exact zeroCurrent_mem_den_locallyAsymptoticallyStable hp hH (by rw [hdM]; exact hB)

/-- **Subcritical boundary points of the family**: `zeroCurrentHopf E R L ω₀ d` is unstable when
`𝔅(d, R/L, ω₀) < 0` (`zeroCurrent_mem_den_unstable`); such `ω₀` exist for every damping ratio
`d < x₀ R/L` (`exists_bautinForm_neg`). -/
@[tmio TM, powerlib_domain] theorem zeroCurrentHopf_mem_den_unstable {E R L w d : ℝ}
    (hE : 0 < E) (hR : 0 < R) (hL : 0 < L) (hw : 0 < w) (hd : 0 < d)
    (hB : bautinForm d (R / L) w < 0) :
    connection% (zeroCurrentHopf E R L w d ∈ family.den (.flow .unstable)) := by
  obtain ⟨hp, hdM, hH⟩ := zeroCurrentHopf_meets hE hR hL hw hd
  unfold zeroCurrentHopf at hp hH ⊢
  exact zeroCurrent_mem_den_unstable hp hH (by rw [hdM]; exact hB)

/-- **A damping ratio above the threshold is supercritical whatever the grid**: every physical
zero-current model on the Hopf boundary with `bautinLow(D/M, R/L) ≥ 0` (`D/M ≥ x₀ R/L`) is locally
asymptotically stable (`bautinForm_pos_of_bautinLow`). -/
@[tmio TM, powerlib_domain] theorem zeroCurrent_mem_den_locallyAsymptoticallyStable_of_bautinLow
    {E R L w M D : ℝ} (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q)
    (hlow : 0 ≤ bautinLow (D / M) (R / L)) :
    connection% (zeroCurrent E R L w M D ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hR := zeroCurrent_R_pos hp hH
  obtain ⟨hN, hM, hD⟩ := hp
  have hL : 0 < L := hN.L
  have hw : 0 < w := hN.ω0
  have hM' : 0 < M := hM
  have hD' : 0 < D := hD
  exact zeroCurrent_mem_den_locallyAsymptoticallyStable ⟨hN, hM, hD⟩ hH
    (bautinForm_pos_of_bautinLow (by positivity) (by positivity) hw hlow)

/-- **The line `X = R` is supercritical**: every physical zero-current model on the Hopf boundary
with `ω₀ L = R` is locally asymptotically stable (`bautinForm_self_pos`). -/
@[tmio TM, powerlib_domain] theorem zeroCurrent_mem_den_locallyAsymptoticallyStable_of_X_eq_R
    {E R L w M D : ℝ} (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q)
    (hX : w * L = R) :
    connection% (zeroCurrent E R L w M D ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hR := zeroCurrent_R_pos hp hH
  obtain ⟨hN, hM, hD⟩ := hp
  have hL : 0 < L := hN.L
  have hM' : 0 < M := hM
  have hD' : 0 < D := hD
  have hw : w = R / L := by
    rw [← hX]
    field_simp
  refine zeroCurrent_mem_den_locallyAsymptoticallyStable ⟨hN, hM, hD⟩ hH ?_
  rw [hw]
  exact bautinForm_self_pos (by positivity) (by positivity)

end VSM
end powerlib.GFM.Line
