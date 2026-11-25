import theorem.GridTiedConverter.GFM.HopfBautinLine

/-! # The Hopf boundary of the zero-current VSM in units of the Hopf period (two parameters)

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* The family `Line.VSM.bautinSurf s w`: zero-current points (`E = V = 1`, `P_ref = 0`, `δ* = 0`)
  with `R = s`, `L = 1`, `ω₀ = w`, `u = s² + w² − 1`, `M = w u/(u² + 4s²)`,
  `D = 2 s w/(u² + 4s²)` (so `D/M = 2s/u`, `E²ω₀/(LM) = (u² + 4s²)/u`), in the physical range
  `s, w > 0`, `u > 0`. Every zero-current point on the Hopf boundary of the quartic is one of
  these after scaling time by its Hopf frequency `ω` and the line current by a constant (the
  study's normalisation `ω = 1`; the scaling is not formalised here). `bautinPath s` is the line
  `w = 1` (`bautinPath_eq_bautinSurf`).
* Content: the operating point, the requirements, the Jacobian, the quartic
  `(z² + 1)(z² + τ z + Δ)` with `τ = 2s(s² + w²)/u`, `Δ = (u² + 4s²)/u`, the explicit critical
  pair at `ω = 1` for every `(s, w)` of the range, and the Bautin polynomial `bautinSurfNum`
  (the numerator of `ℓ₁` on the family). Level: exact rational-function identities.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, the VSM without filter on a dynamic
R–L line); the normalisation, the critical pair and the polynomial were derived with SymPy and
python-flint in exact arithmetic over `ℚ(s, w)` (untrusted, discovery evidence only; every
identity is proved here); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5
(the critical eigenvectors), §8.3 (Bautin points).

Results.
* `Line.VSM.bautinSurf`, `bautinSurf_point` (zero current), `bautinSurf_meets` (balanced and
  physical), `bautinSurf_jac`, `bautinSurf_coeffs` (`a₃ = a₁ = τ`, `a₂ = 1 + Δ`, `a₀ = Δ`),
  `bautinSurf_boundary` (on the Hopf boundary), `bautinSurf_charpoly`.
* The critical pair: `bautinSurfDen` (`|u r(i)|²`, a sum of two squares), `bautinSurfQ`,
  `bautinSurfP`, `bautinSurf_isCriticalPair` (`A q = i q`, `Aᵀ p = −i p`, `⟨p, q⟩ = 1`).
* `bautinSurfNum` (`N(s², w²)`, up to positive factors the numerator of the first coefficient of
  the chart jet on the lines `w = const`, `L1V_eq` of the line modules; the same polynomial as the
  frequency-normalised numerator `ellNum 1 (s²) (w²)` of
  `theorem/GridTiedConverter/GFM/HopfLyapunovSymbolic.lean`, whose Bautin set has the lower
  branch `w < s` and the upper branch `w > s` in these coordinates), `bautinPath_eq_bautinSurf`,
  `bautinSurfNum_one` (on the line `w = 1` it is `bautinNum` up to the factor `s⁴`).
* The stability of Bautin points of the family (second Lyapunov coefficient) along the lines
  `w = 3` and `w = 2` is decided in `theorem/GridTiedConverter/GFM/HopfBautinW3Point.lean` and
  `theorem/GridTiedConverter/GFM/HopfBautinW2Point.lean`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Matrix
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient

/-- **The zero-current Hopf boundary in units of the Hopf period**: `E = V = 1`, `R = s`, `L = 1`,
`ω₀ = w`, `M = w u/(u² + 4s²)`, `D = 2 s w/(u² + 4s²)` with `u = s² + w² − 1`, `P_ref = 0`,
`δ* = 0`. -/
def bautinSurf (s w : ℝ) : Model :=
  ⟨⟨⟨1, 1, s, 1, w⟩, w * (s ^ 2 + w ^ 2 - 1) / ((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2),
    2 * s * w / ((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2), 0⟩, 0⟩

/-- The operating point of the family is the zero-current state. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSurf_point (s w : ℝ) : (bautinSurf s w).point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, bautinSurf, Network.is]

/-- Every point of the family with `s, w > 0`, `s² + w² > 1` is balanced and physical.
Satisfaction of the requirements. -/
@[tmio M, powerlib_domain] theorem bautinSurf_meets {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hu : 0 < s ^ 2 + w ^ 2 - 1) :
    Meets (bautinSurf s w) .balanced ∧ Meets (bautinSurf s w) .physical := by
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · norm_num [Meets, bautinSurf, Network.qssPower, Network.is, Network.power_eq]
  all_goals simp only [bautinSurf]
  all_goals positivity

/-- The Jacobian of the family, `[[0, 1, 0, 0], [0, −2s/u, −(u² + 4s²)/(w u), 0], [0, 0, −s, w],
[1, 0, −w, −s]]`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSurf_jac {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hu : 0 < s ^ 2 + w ^ 2 - 1) :
    (bautinSurf s w).jac = !![0, 1, 0, 0;
      0, -(2 * s / (s ^ 2 + w ^ 2 - 1)),
        -(((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2) / (w * (s ^ 2 + w ^ 2 - 1))), 0;
      0, 0, -s, w; 1, 0, -w, -s] := by
  have hK : (s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 ≠ 0 := by positivity
  have hw0 : w ≠ 0 := hw.ne'
  have hu0 : s ^ 2 + w ^ 2 - 1 ≠ 0 := hu.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.jac, jacobian, bautinSurf, Network.is, Network.reactive_eq, Network.X]
  all_goals field_simp

/-- The coefficients of the quartic: `a₃ = a₁ = τ = 2s(s² + w²)/u`, `a₂ = 1 + Δ`, `a₀ = Δ`,
`Δ = (u² + 4s²)/u`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSurf_coeffs {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hu : 0 < s ^ 2 + w ^ 2 - 1) :
    (bautinSurf s w).g.coeff3 = 2 * s * (s ^ 2 + w ^ 2) / (s ^ 2 + w ^ 2 - 1) ∧
      (bautinSurf s w).g.coeff2 (bautinSurf s w).Q =
        1 + ((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2) / (s ^ 2 + w ^ 2 - 1) ∧
      (bautinSurf s w).g.coeff1 (bautinSurf s w).Q =
        2 * s * (s ^ 2 + w ^ 2) / (s ^ 2 + w ^ 2 - 1) ∧
      (bautinSurf s w).g.coeff0 (bautinSurf s w).Q =
        ((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2) / (s ^ 2 + w ^ 2 - 1) := by
  have hQ : (bautinSurf s w).Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, bautinSurf, Network.is, Network.reactive_eq]
  have hK : (s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 ≠ 0 := by positivity
  have hw0 : w ≠ 0 := hw.ne'
  have hu0 : s ^ 2 + w ^ 2 - 1 ≠ 0 := hu.ne'
  rw [hQ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [coeff3, coeff2, coeff1, coeff0, bautinSurf, Network.ρ, Network.σ, Network.X]
  all_goals (field_simp <;> ring)

/-- Every point of the family lies on the Hopf boundary of the quartic (`a₃, a₁, a₀ > 0`,
`a₃ a₂ a₁ = a₁² + a₃² a₀`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSurf_boundary {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hu : 0 < s ^ 2 + w ^ 2 - 1) :
    0 < (bautinSurf s w).g.coeff3 ∧ 0 < (bautinSurf s w).g.coeff1 (bautinSurf s w).Q ∧
      0 < (bautinSurf s w).g.coeff0 (bautinSurf s w).Q ∧
      (bautinSurf s w).g.coeff3 * (bautinSurf s w).g.coeff2 (bautinSurf s w).Q *
          (bautinSurf s w).g.coeff1 (bautinSurf s w).Q =
        (bautinSurf s w).g.coeff1 (bautinSurf s w).Q ^ 2 +
          (bautinSurf s w).g.coeff3 ^ 2 * (bautinSurf s w).g.coeff0 (bautinSurf s w).Q := by
  obtain ⟨h3, h2, h1, h0⟩ := bautinSurf_coeffs hs hw hu
  rw [h3, h2, h1, h0]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  have hu0 : s ^ 2 + w ^ 2 - 1 ≠ 0 := hu.ne'
  field_simp

/-- **Hopf points**: `det(zI − J) = (z² + 1)(z² + τ z + Δ)` on the family. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bautinSurf_charpoly {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hu : 0 < s ^ 2 + w ^ 2 - 1) (z : ℂ) :
    (Linear.characteristicMatrix (bautinSurf s w).jac z).det =
      (z ^ 2 + 1) * (z ^ 2 + ((2 * s * (s ^ 2 + w ^ 2) / (s ^ 2 + w ^ 2 - 1) : ℝ) : ℂ) * z +
        ((((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2) / (s ^ 2 + w ^ 2 - 1) : ℝ) : ℂ)) := by
  obtain ⟨h3, h2, h1, h0⟩ := bautinSurf_coeffs hs hw hu
  rw [Model.det_characteristicMatrix, h3, h2, h1, h0]
  push_cast
  ring

/-- `|u r(i)|² = (u² + 4s² − u)² + 4s²(s² + w²)²`, `r(z) = z² + τ z + Δ` the stable factor. -/
def bautinSurfDen (s w : ℝ) : ℝ :=
  ((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 - (s ^ 2 + w ^ 2 - 1)) ^ 2 +
    4 * s ^ 2 * (s ^ 2 + w ^ 2) ^ 2

/-- The critical right eigenvector `q = (u² + 4s², i(u² + 4s²), w(u − 2is), (s + i)(u − 2is))`. -/
def bautinSurfQ (s w : ℝ) : Fin 4 → ℂ :=
  ![(((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 : ℝ) : ℂ),
    (((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 : ℝ) : ℂ) * I,
    ((w * (s ^ 2 + w ^ 2 - 1) : ℝ) : ℂ) + ((-2 * s * w : ℝ) : ℂ) * I,
    ((s * (s ^ 2 + w ^ 2 + 1) : ℝ) : ℂ) + ((s ^ 2 + w ^ 2 - 1 - 2 * s ^ 2 : ℝ) : ℂ) * I]

/-- The critical left eigenvector, `⟨p, q⟩ = 1`. -/
def bautinSurfP (s w : ℝ) : Fin 4 → ℂ :=
  ![(((s ^ 4 + 2 * s ^ 2 * w ^ 2 + s ^ 2 + w ^ 4 - 3 * w ^ 2 + 2) / (2 * bautinSurfDen s w) :
        ℝ) : ℂ) + ((s * (s ^ 2 + w ^ 2) / bautinSurfDen s w : ℝ) : ℂ) * I,
    ((2 * s * (s ^ 2 - w ^ 2 + 1) * (s ^ 2 + w ^ 2 - 1) /
        ((s ^ 2 + (w - 1) ^ 2) * (s ^ 2 + (w + 1) ^ 2) * bautinSurfDen s w) : ℝ) : ℂ) +
      (((s ^ 2 + w ^ 2 - 1) * (s ^ 6 + 3 * s ^ 4 * w ^ 2 + 4 * s ^ 4 + 3 * s ^ 2 * w ^ 4 + s ^ 2 +
        w ^ 6 - 4 * w ^ 4 + 5 * w ^ 2 - 2) /
        (2 * (s ^ 2 + (w - 1) ^ 2) * (s ^ 2 + (w + 1) ^ 2) * bautinSurfDen s w) : ℝ) : ℂ) * I,
    (((s ^ 2 - w ^ 2 + 1) * (s ^ 2 + w ^ 2 - 2) / (2 * w * bautinSurfDen s w) : ℝ) : ℂ) +
      ((-(s * (s ^ 4 + 2 * s ^ 2 * w ^ 2 + 3 * s ^ 2 + w ^ 4 - w ^ 2 + 2)) /
        (2 * w * bautinSurfDen s w) : ℝ) : ℂ) * I,
    ((s * (s ^ 2 + w ^ 2) / bautinSurfDen s w : ℝ) : ℂ) +
      ((-(s ^ 4 + 2 * s ^ 2 * w ^ 2 + s ^ 2 + w ^ 4 - 3 * w ^ 2 + 2) / (2 * bautinSurfDen s w) :
        ℝ) : ℂ) * I]

@[tmio M, powerlib_domain] private theorem bautinSurf_jacobianC {s w : ℝ} (hs : 0 < s)
    (hw : 0 < w) (hu : 0 < s ^ 2 + w ^ 2 - 1) :
    jacobianC (bautinSurf s w).field 0 =
      (!![0, 1, 0, 0;
        0, -(2 * s / (s ^ 2 + w ^ 2 - 1)),
          -(((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2) / (w * (s ^ 2 + w ^ 2 - 1))), 0;
        0, 0, -s, w; 1, 0, -w, -s] : Matrix (Fin 4) (Fin 4) ℝ).map (fun x => (x : ℂ)) := by
  rw [Model.jacobianC_field, bautinSurf_jac hs hw hu]
  rfl

/-- **The critical pair** of the family at `ω₀ = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinSurf_isCriticalPair {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hu : 0 < s ^ 2 + w ^ 2 - 1) :
    IsCriticalPair (bautinSurf s w).field 0 1 (bautinSurfQ s w) (bautinSurfP s w) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hu0 : s ^ 2 + w ^ 2 - 1 ≠ 0 := hu.ne'
  have hD : ((s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 - (s ^ 2 + w ^ 2 - 1)) ^ 2 +
      4 * s ^ 2 * (s ^ 2 + w ^ 2) ^ 2 ≠ 0 := by positivity
  have hZ' : 0 < (s ^ 2 + w ^ 2 + 1) ^ 2 - 4 * w ^ 2 := by
    have : (s ^ 2 + w ^ 2 + 1) ^ 2 - 4 * w ^ 2 = (s ^ 2 + (w - 1) ^ 2) * (s ^ 2 + (w + 1) ^ 2) := by
      ring
    rw [this]; positivity
  have hZ : (s ^ 2 + w ^ 2 + 1) ^ 2 - 4 * w ^ 2 ≠ 0 := hZ'.ne'
  have hZ2 : (s ^ 2 + w ^ 2 + 1) ^ 2 - w ^ 2 * 4 ≠ 0 := by rw [mul_comm]; exact hZ
  have hK : (s ^ 2 + w ^ 2 - 1) ^ 2 + 4 * s ^ 2 ≠ 0 := by positivity
  refine ⟨?_, one_pos, ?_, ?_, ?_⟩
  · have hf : (bautinSurf s w).field = (bautinSurf s w).g.field := by
      funext z; simp [Model.field, bautinSurf_point]
    rw [hf]
    ext i
    fin_cases i <;> norm_num [field, bautinSurf, Network.power_eq, Network.rateD,
      Network.rateQ, Network.X]
  · rw [bautinSurf_jacobianC hs hw hu]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, bautinSurfQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring
  · rw [bautinSurf_jacobianC hs hw hu]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, bautinSurfP, bautinSurfDen,
      Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring
  · simp [dotProduct, Fin.sum_univ_four, bautinSurfP, bautinSurfQ, bautinSurfDen, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring

/-- **The path `bautinPath` is the line `w = 1` of the family.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_eq_bautinSurf {s : ℝ} (hs : s ≠ 0) :
    bautinPath s = bautinSurf s 1 := by
  have h4 : 4 + s ^ 2 ≠ 0 := by positivity
  have h4' : (s ^ 2 + 1 ^ 2 - 1) ^ 2 + 4 * s ^ 2 ≠ 0 := by positivity
  simp only [bautinPath, bautinSurf, Model.mk.injEq, VSM.mk.injEq, and_true, true_and]
  constructor <;> field_simp <;> ring

/-- **The Bautin polynomial of the family**, `N(s², w²)`: up to positive factors the numerator of
the first coefficient of the chart jet on the lines `w = const` (the polynomial `ellNum 1 (s²) (w²)`
of the zero-current closed form). -/
def bautinSurfNum (s w : ℝ) : ℝ :=
  -35 + 45 * s ^ 2 + 153 * w ^ 2 + 123 * s ^ 4 - 114 * s ^ 2 * w ^ 2 - 281 * w ^ 4 - 49 * s ^ 6 -
    371 * s ^ 4 * w ^ 2 + 73 * s ^ 2 * w ^ 4 + 299 * w ^ 6 - 101 * s ^ 8 + 12 * s ^ 6 * w ^ 2 +
    330 * s ^ 4 * w ^ 4 - 68 * s ^ 2 * w ^ 6 - 221 * w ^ 8 + 3 * s ^ 10 + 107 * s ^ 8 * w ^ 2 +
    70 * s ^ 6 * w ^ 4 + 14 * s ^ 4 * w ^ 6 + 167 * s ^ 2 * w ^ 8 + 119 * w ^ 10 + 13 * s ^ 12 -
    10 * s ^ 10 * w ^ 2 - 113 * s ^ 8 * w ^ 4 - 188 * s ^ 6 * w ^ 6 - 181 * s ^ 4 * w ^ 8 -
    122 * s ^ 2 * w ^ 10 - 39 * w ^ 12 + s ^ 14 - s ^ 12 * w ^ 2 - 15 * s ^ 10 * w ^ 4 -
    25 * s ^ 8 * w ^ 6 - 5 * s ^ 6 * w ^ 8 + 21 * s ^ 4 * w ^ 10 + 19 * s ^ 2 * w ^ 12 +
    5 * w ^ 14

/-- On the line `w = 1` the Bautin polynomial is `s⁴ bautinNum s`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bautinSurfNum_one (s : ℝ) :
    bautinSurfNum s 1 = s ^ 4 * bautinNum s := by
  unfold bautinSurfNum bautinNum
  ring

end VSM
end powerlib.GFM.Line
