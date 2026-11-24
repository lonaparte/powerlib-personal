import theorem.GridTiedConverter.GFM.HopfLineInstability
import theorem.Dynamics.CenterReductionBautin

/-! # Degenerate Hopf points (`ℓ₁ = 0`) of the VSM on a dynamic R–L line (four states)

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* Parameter range: the one-parameter path `Line.VSM.bautinPath s` (`s > 0`) of zero-current
  points on the Hopf boundary of the quartic, `E = V = 1`, `R = s`, `L = 1`, `ω₀ = 1` (`X = 1`),
  `M = 1/(4 + s²)`, `D = 2/(s(4 + s²))`, `P_ref = 0`, `δ* = 0`: every point is balanced and
  physical, with characteristic polynomial `(z² + 1)(z² + (2s + 2/s) z + 4 + s²)` (eigenvalues
  `±i` and a stable pair). `ℓ₁` is Kuznetsov's first Lyapunov coefficient `firstLyapunov` of the
  model field at the explicit critical pair `(bautinPathQ s, bautinPathP s)` (`⟨p, q⟩ = 1`,
  `q` not normalised: `ℓ₁` scales by `|c|²`, its sign is a property of the model,
  `Line.VSM.Model.sign_firstLyapunov_eq_of_boundary`).
* Level: exact rational-function identities along the path, the sign of `ℓ₁`, the existence of
  its zero, and Lyapunov instability / local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) where `ℓ₁ ≠ 0`. Not stated: the stability of the degenerate point
  itself (it needs the second Lyapunov coefficient of the reduced field, see below), the
  bifurcating cycles, the `ε = 1/ω_b` law of the source note.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, the VSM without filter on a dynamic
R–L line; both signs of `ℓ₁` on the boundary,
`theorem/GridTiedConverter/GFM/HopfCoefficientLine.lean`);
the path and its closed forms were found with SymPy (untrusted, discovery evidence only);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5, §5.4 (the projection formula)
and §8.3 (Bautin points, `ℓ₁ = 0`). The generic laws are
`theorem/GridTiedConverter/GFM/HopfLineInstability.lean` (the family laws for `ℓ₁ ≠ 0`); the
second-coefficient laws are `theorem/Dynamics/Degenerate/PlanarFocus2.lean` and
`theorem/Dynamics/CenterReductionBautin.lean`.

Results.
* The path and its data: `Line.VSM.bautinPath`, `bautinPath_point` (zero current),
  `bautinPath_meets` (balanced and physical), `bautinPath_jac`, `bautinPath_coeffs`
  (`a₃ = a₁ = 2s + 2/s`, `a₂ = s² + 5`, `a₀ = 4 + s²`: on the boundary),
  `bautinPath_charpoly`, `bautinPath_isCriticalPair` (`q = (s(4 + s²), i s(4 + s²), s − 2i,
  s² + 2 − is)` and the explicit `p`).
* `bautinPath_firstLyapunov`: `ℓ₁ = s³(s² + 4)² N(s)/(D₁(s) D₂(s))` with
  `N(s) = s¹⁰ + 12s⁸ − 22s⁶ − 132s⁴ − 160s² − 64` (`bautinNum`),
  `D₁ = s⁶ + 10s⁴ + 17s² + 4`, `D₂ = s⁶ + 16s⁴ + 32s² + 16`; `bautinPath_sign_firstLyapunov`
  (`sign ℓ₁ = sign N(s)`), `bautinNum_neg` (`0 < s ≤ 2`), `bautinNum_pos` (`s ≥ 21/10`).
* **Degenerate points exist**: `exists_bautinPath_firstLyapunov_eq_zero` (a zero
  `s* ∈ (2, 21/10)` of `N`, `ℓ₁ = 0` there) and `exists_boundary_firstLyapunov_eq_zero` (a
  balanced physical model on the Hopf boundary with a critical pair and `ℓ₁ = 0`); the zero is
  unique (`bautinNum_strictMonoOn`, `existsUnique_bautinNum_eq_zero`) and the path has exactly
  one transition, `sign ℓ₁(s) = sign(s − s*)` (`exists_sign_firstLyapunov_eq_sign_sub`). The zero is
  algebraic (`t = s*²` is the positive root of `t⁵ + 12t⁴ − 22t³ − 132t² − 160t − 64`); a
  search found no rational zero-current point with `ℓ₁ = 0` (SymPy, small heights).
* Not proved: the stability of the degenerate point. Its second Lyapunov coefficient, computed in
  floating point (SymPy, centre manifold to order four, untrusted), is positive (`l₂ ≈ 8.9·10³`
  in the chart of `bautinPathQ`), i.e. an unstable weak focus of the second order; the Lean
  decision needs the order-four approximate centre manifold `φ` of the model at `s*` with
  invariance defect `O(‖u‖⁵)` and the 5-jet of its chart field in exact arithmetic over
  `ℚ(s*)`: the hypotheses of `Line.VSM.mem_den_unstable_of_secondLyapunov_pos`.

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.bautinPath_mem_den_locallyAsymptoticallyStable`: for `0 < s ≤ 2` the boundary point
  is locally asymptotically stable (`ℓ₁ < 0`).
* `Line.VSM.bautinPath_mem_den_unstable`: for `s ≥ 21/10` the boundary point is unstable
  (`ℓ₁ > 0`).
* `Line.VSM.mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`,
  `Line.VSM.mem_den_unstable_of_secondLyapunov_pos`: a boundary model with a critical pair, an
  approximate centre manifold `φ` (invariance defect `O(‖u‖⁵)`) and the quintic jet `J` of its
  chart field in the critical chart with `l₁(J) = 0` is locally asymptotically stable if
  `l₂(J) < 0` and unstable if `l₂(J) > 0`
  (`Dynamics.CenterManifold.localAsymptoticStable_of_l2_neg_of_charpoly`,
  `unstable_of_l2_pos_of_charpoly`, `theorem/Dynamics/CenterReductionBautin.lean`).
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Matrix
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

/-- **The path of zero-current boundary points**: `E = V = 1`, `R = s`, `L = 1`, `ω₀ = 1`
(`X = 1`), `M = 1/(4 + s²)`, `D = 2/(s(4 + s²))`, `P_ref = 0`, `δ* = 0`. -/
def bautinPath (s : ℝ) : Model := ⟨⟨⟨1, 1, s, 1, 1⟩, 1 / (4 + s ^ 2), 2 / (s * (4 + s ^ 2)), 0⟩, 0⟩

/-- The operating point of the path is the zero-current state. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_point (s : ℝ) : (bautinPath s).point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, bautinPath, Network.is]

/-- Every point of the path (`s > 0`) is balanced and physical. Satisfaction of the
requirements. -/
@[tmio M, powerlib_domain] theorem bautinPath_meets {s : ℝ} (hs : 0 < s) :
    Meets (bautinPath s) .balanced ∧ Meets (bautinPath s) .physical := by
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · norm_num [Meets, bautinPath, Network.qssPower, Network.is, Network.power_eq]
  all_goals simp only [bautinPath]
  all_goals positivity

/-- The Jacobian along the path, `[[0, 1, 0, 0], [0, −2/s, −(4 + s²), 0], [0, 0, −s, 1],
[1, 0, −1, −s]]`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_jac {s : ℝ} (hs : 0 < s) :
    (bautinPath s).jac = !![0, 1, 0, 0; 0, -(2 / s), -(4 + s ^ 2), 0; 0, 0, -s, 1;
      1, 0, -1, -s] := by
  have h4 : (4 + s ^ 2) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.jac, jacobian, bautinPath, Network.is, Network.reactive_eq, Network.X]
  field_simp

/-- The coefficients of the quartic along the path: `a₃ = a₁ = 2s + 2/s`, `a₂ = s² + 5`,
`a₀ = 4 + s²`, on the Hopf boundary `a₃ a₂ a₁ = a₁² + a₃² a₀`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_coeffs {s : ℝ} (hs : 0 < s) :
    (bautinPath s).g.coeff3 = 2 * s + 2 / s ∧ (bautinPath s).g.coeff2 (bautinPath s).Q = s ^ 2 + 5 ∧
      (bautinPath s).g.coeff1 (bautinPath s).Q = 2 * s + 2 / s ∧
      (bautinPath s).g.coeff0 (bautinPath s).Q = 4 + s ^ 2 := by
  have hQ : (bautinPath s).Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, bautinPath, Network.is, Network.reactive_eq]
  have h4 : (4 + s ^ 2) ≠ 0 := by positivity
  rw [hQ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [coeff3, coeff2, coeff1, coeff0, bautinPath, Network.ρ, Network.σ, Network.X]
  all_goals field_simp
  all_goals ring


/-- `D₁(s) = s⁶ + 10s⁴ + 17s² + 4`. -/
def bautinDen1 (s : ℝ) : ℝ := s ^ 6 + 10 * s ^ 4 + 17 * s ^ 2 + 4

/-- `D₂(s) = s⁶ + 16s⁴ + 32s² + 16`. -/
def bautinDen2 (s : ℝ) : ℝ := s ^ 6 + 16 * s ^ 4 + 32 * s ^ 2 + 16

/-- `N(s) = s¹⁰ + 12s⁸ − 22s⁶ − 132s⁴ − 160s² − 64`. -/
def bautinNum (s : ℝ) : ℝ :=
  s ^ 10 + 12 * s ^ 8 - 22 * s ^ 6 - 132 * s ^ 4 - 160 * s ^ 2 - 64

/-- The critical right eigenvector. -/
def bautinPathQ (s : ℝ) : Fin 4 → ℂ :=
  ![((s * (4 + s ^ 2) : ℝ) : ℂ), ((s * (4 + s ^ 2) : ℝ) : ℂ) * I, (s : ℂ) + ((-2 : ℝ) : ℂ) * I,
    ((s ^ 2 + 2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I]

/-- The critical left eigenvector, `⟨p, q⟩ = 1`. -/
def bautinPathP (s : ℝ) : Fin 4 → ℂ :=
  ![((s * (s ^ 2 + 3) / (2 * bautinDen1 s) : ℝ) : ℂ) + (((s ^ 2 + 1) / bautinDen1 s : ℝ) : ℂ) * I,
    ((2 * s ^ 2 / ((s ^ 2 + 4) * bautinDen1 s) : ℝ) : ℂ) +
      ((s * (s ^ 4 + 7 * s ^ 2 + 4) / (2 * (s ^ 2 + 4) * bautinDen1 s) : ℝ) : ℂ) * I,
    ((s * (s ^ 2 - 1) / (2 * bautinDen1 s) : ℝ) : ℂ) +
      ((-(s ^ 4 + 5 * s ^ 2 + 2) / (2 * bautinDen1 s) : ℝ) : ℂ) * I,
    (((s ^ 2 + 1) / bautinDen1 s : ℝ) : ℂ) +
      ((-(s * (s ^ 2 + 3)) / (2 * bautinDen1 s) : ℝ) : ℂ) * I]

/-- **Hopf points**: `det(zI − J) = (z² + 1)(z² + (2s + 2/s) z + 4 + s²)` along the path.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_charpoly {s : ℝ} (hs : 0 < s) (z : ℂ) :
    (Linear.characteristicMatrix (bautinPath s).jac z).det =
      (z ^ 2 + 1) * (z ^ 2 + ((2 * s + 2 / s : ℝ) : ℂ) * z + ((4 + s ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨h3, h2, h1, h0⟩ := bautinPath_coeffs hs
  rw [Model.det_characteristicMatrix, h3, h2, h1, h0]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem bautinPath_jacobianC {s : ℝ} (hs : 0 < s) :
    jacobianC (bautinPath s).field 0 =
      (!![0, 1, 0, 0; 0, -(2 / s), -(4 + s ^ 2), 0; 0, 0, -s, 1; 1, 0, -1, -s] :
        Matrix (Fin 4) (Fin 4) ℝ).map (fun x => (x : ℂ)) := by
  rw [Model.jacobianC_field, bautinPath_jac hs]
  rfl

@[tmio M, powerlib_domain] private theorem bautinPath_bilinC (s : ℝ) (u w : Fin 4 → ℂ) :
    bilinC (bautinPath s).field 0 u w =
      ![0, -((4 + s ^ 2 : ℝ) : ℂ) * (u 0 * w 3 + u 3 * w 0), -(u 0 * w 0), 0] := by
  have hf : (bautinPath s).field = (bautinPath s).g.field := by
    funext z; simp [Model.field, bautinPath_point]
  have h4 : (4 + s ^ 2) ≠ 0 := by positivity
  rw [hf, bilinC_field_zero]
  ext i
  fin_cases i <;> simp [bautinPath]

@[tmio M, powerlib_domain] private theorem bautinPath_trilinC (s : ℝ) (u w z : Fin 4 → ℂ) :
    trilinC (bautinPath s).field 0 u w z =
      ![0, ((4 + s ^ 2 : ℝ) : ℂ) * (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0), 0,
        -(u 0 * w 0 * z 0)] := by
  have hf : (bautinPath s).field = (bautinPath s).g.field := by
    funext z; simp [Model.field, bautinPath_point]
  rw [hf, trilinC_field_zero]
  ext i
  fin_cases i <;> simp [bautinPath]

/-- **The critical pair** along the path, at `ω₀ = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_isCriticalPair {s : ℝ} (hs : 0 < s) :
    IsCriticalPair (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hD : s ^ 6 + 10 * s ^ 4 + 17 * s ^ 2 + 4 ≠ 0 := by positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  have h4' : 4 + s ^ 2 ≠ 0 := by positivity
  refine ⟨?_, one_pos, ?_, ?_, ?_⟩
  · have hf : (bautinPath s).field = (bautinPath s).g.field := by
      funext z; simp [Model.field, bautinPath_point]
    rw [hf]
    ext i
    fin_cases i <;> norm_num [field, bautinPath, Network.power_eq, Network.rateD,
      Network.rateQ, Network.X]
  · rw [bautinPath_jacobianC hs]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, bautinPathQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring
  · rw [bautinPath_jacobianC hs]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, bautinPathP, bautinDen1,
      Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring
  · simp [dotProduct, Fin.sum_univ_four, bautinPathP, bautinPathQ, bautinDen1, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring

/-- **The first Lyapunov coefficient along the path**:
`ℓ₁ = s³(s² + 4)² N(s)/(D₁(s) D₂(s))`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_firstLyapunov {s : ℝ} (hs : 0 < s) :
    firstLyapunov (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s) =
      s ^ 3 * (s ^ 2 + 4) ^ 2 * bautinNum s / (bautinDen1 s * bautinDen2 s) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hD : s ^ 6 + 10 * s ^ 4 + 17 * s ^ 2 + 4 ≠ 0 := by positivity
  have hD2 : s ^ 6 + 16 * s ^ 4 + 32 * s ^ 2 + 16 ≠ 0 := by positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  have h4' : 4 + s ^ 2 ≠ 0 := by positivity
  set r : Fin 4 → ℂ := ![((s * (s ^ 2 + 4) * (s ^ 4 + 2 * s ^ 2 + 4) : ℝ) : ℂ), 0,
    ((2 * s * (s ^ 2 + 2) * (s ^ 2 + 4) : ℝ) : ℂ), ((s ^ 4 * (s ^ 2 + 4) : ℝ) : ℂ)] with hr_def
  set S : Fin 4 → ℂ :=
    ![((s ^ 3 * (s ^ 2 + 2) ^ 2 * (s ^ 2 + 4) ^ 2 * (s ^ 2 + 14) / (3 * bautinDen2 s) : ℝ) : ℂ) +
        ((2 * s ^ 2 * (s ^ 2 + 4) ^ 2 * (s ^ 4 + 20 * s ^ 2 + 24) / (3 * bautinDen2 s) : ℝ) :
          ℂ) * I,
      ((-4 * s ^ 2 * (s ^ 2 + 4) ^ 2 * (s ^ 4 + 20 * s ^ 2 + 24) / (3 * bautinDen2 s) : ℝ) : ℂ) +
        ((2 * s ^ 3 * (s ^ 2 + 2) ^ 2 * (s ^ 2 + 4) ^ 2 * (s ^ 2 + 14) / (3 * bautinDen2 s) : ℝ) :
          ℂ) * I,
      ((-2 * s ^ 3 * (s ^ 2 + 4) ^ 2 * (s ^ 4 + 14 * s ^ 2 + 12) / (3 * bautinDen2 s) : ℝ) : ℂ) +
        ((2 * s ^ 2 * (s ^ 2 + 4) ^ 2 * (s ^ 4 + 12 * s ^ 2 + 8) / (3 * bautinDen2 s) : ℝ) : ℂ) * I,
      ((s ^ 2 * (s ^ 2 + 4) ^ 2 * (s ^ 6 + 16 * s ^ 4 + 24 * s ^ 2 + 16) / (3 * bautinDen2 s) : ℝ) :
          ℂ) +
        ((-2 * s ^ 3 * (s ^ 2 + 4) ^ 2 * (s ^ 4 + 16 * s ^ 2 + 16) / (3 * bautinDen2 s) : ℝ) : ℂ) *
          I] with hS_def
  have hA : IsUnit (jacobianC (bautinPath s).field 0).det := by
    have h := bautinPath_charpoly hs 0
    rw [Linear.characteristicMatrix, zero_smul, zero_sub, Matrix.det_neg,
      ← Model.jacobianC_field (bautinPath s)] at h
    norm_num at h
    rw [h]
    refine isUnit_iff_ne_zero.mpr fun h0 => h4' ?_
    have h1 := congrArg Complex.re h0
    simpa [← Complex.ofReal_pow] using h1
  have h2 : IsUnit (shift2 (jacobianC (bautinPath s).field 0) 1).det := by
    have h := bautinPath_charpoly hs (2 * I)
    rw [Linear.characteristicMatrix, ← Model.jacobianC_field (bautinPath s)] at h
    rw [shift2, show ((2 * (1 : ℝ) : ℂ) * I) = 2 * I by push_cast; ring, h]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := congrArg Complex.re h0
    simp [pow_two] at h1
    rcases h1 with h1 | h1
    · norm_num at h1
    · nlinarith
  have hr : jacobianC (bautinPath s).field 0 *ᵥ r =
      bilinC (bautinPath s).field 0 (bautinPathQ s) (star (bautinPathQ s)) := by
    rw [bautinPath_jacobianC hs, bautinPath_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, bautinPathQ, r,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals first | ring1 | simp
  have hs' : shift2 (jacobianC (bautinPath s).field 0) 1 *ᵥ S =
      bilinC (bautinPath s).field 0 (bautinPathQ s) (bautinPathQ s) := by
    rw [bautinPath_jacobianC hs, bautinPath_bilinC, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, bautinPathQ, S, bautinDen2,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals field_simp
    all_goals ring
  rw [firstLyapunov_eq_of_solve hA h2 hr hs', bautinPath_trilinC, bautinPath_bilinC,
    bautinPath_bilinC]
  simp [pairing_apply, Fin.sum_univ_four, bautinPathP, bautinPathQ, r, S, bautinDen1, bautinDen2,
    bautinNum, Complex.mul_re, Complex.mul_im, -Complex.ofReal_mul, -Complex.ofReal_div,
    -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring


/-! ## The sign of `ℓ₁` along the path and its zero -/

/-- `N(s) < 0` for `0 < s ≤ 2` (`N = (t − 4)(t⁴ + 16t³ + 42t² + 36t − 16) − 128`, `t = s²`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinNum_neg {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) :
    bautinNum s < 0 := by
  have ht : s ^ 2 ≤ 4 := by nlinarith
  have hg : 0 ≤ (s ^ 2) ^ 4 + 16 * (s ^ 2) ^ 3 + 42 * (s ^ 2) ^ 2 + 36 * s ^ 2 := by positivity
  have h := mul_nonneg (sub_nonneg.mpr ht) hg
  unfold bautinNum
  nlinarith

/-- `N(s) > 0` for `s ≥ 21/10` (`N(s) − N(21/10)` is `(s² − 441/100)` times a polynomial with
positive coefficients in `s²`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinNum_pos {s : ℝ} (hs : 21 / 10 ≤ s) :
    0 < bautinNum s := by
  have ht : 441 / 100 ≤ s ^ 2 := by nlinarith
  have hg : 0 ≤ (s ^ 2) ^ 4 + 1641 / 100 * (s ^ 2) ^ 3 + 503681 / 10000 * (s ^ 2) ^ 2 +
      90123321 / 1000000 * s ^ 2 + 23744384561 / 100000000 := by positivity
  have h := mul_nonneg (sub_nonneg.mpr ht) hg
  unfold bautinNum
  nlinarith

/-- **The sign of `ℓ₁` along the path is the sign of `N(s)`.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_sign_firstLyapunov {s : ℝ} (hs : 0 < s) :
    SignType.sign (firstLyapunov (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s)) =
      SignType.sign (bautinNum s) := by
  have hpos : 0 < s ^ 3 * (s ^ 2 + 4) ^ 2 / (bautinDen1 s * bautinDen2 s) := by
    unfold bautinDen1 bautinDen2; positivity
  rw [bautinPath_firstLyapunov hs, show s ^ 3 * (s ^ 2 + 4) ^ 2 * bautinNum s /
      (bautinDen1 s * bautinDen2 s) = s ^ 3 * (s ^ 2 + 4) ^ 2 / (bautinDen1 s * bautinDen2 s) *
        bautinNum s by ring, sign_mul, sign_pos hpos, one_mul]

/-- **A degenerate Hopf point on the path**: `N` has a zero `s* ∈ (2, 21/10)`, where `ℓ₁ = 0`
(intermediate values of the polynomial `N`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_bautinPath_firstLyapunov_eq_zero :
    ∃ s ∈ Set.Ioo (2 : ℝ) (21 / 10), bautinNum s = 0 ∧
      firstLyapunov (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s) = 0 := by
  have hcont : ContinuousOn bautinNum (Set.Icc (2 : ℝ) (21 / 10)) := by
    unfold bautinNum; fun_prop
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc (by norm_num) hcont
    ⟨(bautinNum_neg (by norm_num) le_rfl).le, (bautinNum_pos le_rfl).le⟩
  have h2 : s ≠ 2 := fun h => by
    rw [h] at hs0; linarith [bautinNum_neg (s := 2) (by norm_num) le_rfl]
  have h21 : s ≠ 21 / 10 := fun h => by
    rw [h] at hs0; linarith [bautinNum_pos (s := 21 / 10) le_rfl]
  refine ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm h2), lt_of_le_of_ne hs.2 h21⟩, hs0, ?_⟩
  rw [bautinPath_firstLyapunov (by linarith [hs.1]), hs0, mul_zero, zero_div]

/-- `N` is strictly increasing for `s ≥ 2` (its difference quotient in `t = s²` is a polynomial
with positive coefficients in `t − 4`, `t' − 4`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinNum_strictMonoOn : StrictMonoOn bautinNum (Set.Ici 2) := by
  intro a ha b hb hab
  have ha2 : (2 : ℝ) ≤ a := ha
  have hx : 0 ≤ a ^ 2 - 4 := by nlinarith
  have hy : 0 ≤ b ^ 2 - 4 := by nlinarith
  have hab2 : 0 < b ^ 2 - a ^ 2 := by nlinarith
  set x := a ^ 2 - 4 with hxd
  set y := b ^ 2 - 4 with hyd
  have key : bautinNum b - bautinNum a = (b ^ 2 - a ^ 2) * (x ^ 4 + x ^ 3 * y + 32 * x ^ 3 +
      x ^ 2 * y ^ 2 + 32 * x ^ 2 * y + 330 * x ^ 2 + x * y ^ 3 + 32 * x * y ^ 2 + 330 * x * y +
      1396 * x + y ^ 4 + 32 * y ^ 3 + 330 * y ^ 2 + 1396 * y + 2080) := by
    simp only [bautinNum, hxd, hyd]
    ring
  have hQ : 0 < x ^ 4 + x ^ 3 * y + 32 * x ^ 3 + x ^ 2 * y ^ 2 + 32 * x ^ 2 * y + 330 * x ^ 2 +
      x * y ^ 3 + 32 * x * y ^ 2 + 330 * x * y + 1396 * x + y ^ 4 + 32 * y ^ 3 + 330 * y ^ 2 +
      1396 * y + 2080 := by
    have := mul_nonneg hx hy
    nlinarith [pow_nonneg hx 2, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hy 2,
      pow_nonneg hy 3, pow_nonneg hy 4, mul_nonneg (pow_nonneg hx 3) hy,
      mul_nonneg (pow_nonneg hx 2) (pow_nonneg hy 2), mul_nonneg hx (pow_nonneg hy 3),
      mul_nonneg (pow_nonneg hx 2) hy, mul_nonneg hx (pow_nonneg hy 2)]
  nlinarith [mul_pos hab2 hQ]

/-- **The degenerate point of the path is unique**: `N` has exactly one positive zero. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem existsUnique_bautinNum_eq_zero :
    ∃! s : ℝ, 0 < s ∧ bautinNum s = 0 := by
  obtain ⟨s, hs, hN, -⟩ := exists_bautinPath_firstLyapunov_eq_zero
  refine ⟨s, ⟨by linarith [hs.1], hN⟩, fun s' ⟨hs'0, hs'N⟩ => ?_⟩
  have h2 : 2 < s' := by
    by_contra h
    linarith [bautinNum_neg hs'0 (not_lt.mp h)]
  exact bautinNum_strictMonoOn.injOn (Set.mem_Ici.mpr h2.le) (Set.mem_Ici.mpr hs.1.le)
    (hs'N.trans hN.symm)

/-- **One transition along the path**: there is `s* ∈ (2, 21/10)` with
`sign ℓ₁(s) = sign(s − s*)` for every `s > 0` — supercritical below `s*`, subcritical above, and
`ℓ₁ = 0` only at `s*`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_sign_firstLyapunov_eq_sign_sub :
    ∃ s₀ ∈ Set.Ioo (2 : ℝ) (21 / 10), ∀ s, 0 < s →
      SignType.sign (firstLyapunov (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s)) =
        SignType.sign (s - s₀) := by
  obtain ⟨s₀, hs₀, hN, -⟩ := exists_bautinPath_firstLyapunov_eq_zero
  refine ⟨s₀, hs₀, fun s hs => ?_⟩
  rw [bautinPath_sign_firstLyapunov hs]
  rcases le_or_gt s 2 with h | h
  · rw [sign_neg (bautinNum_neg hs h), sign_neg (by linarith [hs₀.1])]
  · have hmono := bautinNum_strictMonoOn
    have hs2 : s ∈ Set.Ici (2 : ℝ) := Set.mem_Ici.mpr h.le
    have hs₀2 : s₀ ∈ Set.Ici (2 : ℝ) := Set.mem_Ici.mpr hs₀.1.le
    rcases lt_trichotomy s s₀ with hl | he | hg
    · rw [sign_neg (by rw [← hN]; exact hmono hs2 hs₀2 hl), sign_neg (by linarith)]
    · rw [he, hN, sub_self]
    · rw [sign_pos (by rw [← hN]; exact hmono hs₀2 hs2 hg), sign_pos (by linarith)]

/-- **The physical Hopf boundary contains points with `ℓ₁ = 0`**: a balanced physical model on the
Hopf boundary of the quartic (`a₃, a₁, a₀ > 0`, `a₃ a₂ a₁ = a₁² + a₃² a₀`) with a critical pair
whose first Lyapunov coefficient vanishes (a point of the path, `s* ∈ (2, 21/10)`), where neither
`mem_den_unstable_of_firstLyapunov_pos` nor
`mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg` applies. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_boundary_firstLyapunov_eq_zero :
    ∃ m : Model, Meets m .balanced ∧ Meets m .physical ∧ 0 < m.g.coeff3 ∧
      0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
      m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
        m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q ∧
      ∃ q p : Fin 4 → ℂ, IsCriticalPair m.field 0 1 q p ∧ firstLyapunov m.field 0 1 q p = 0 := by
  obtain ⟨s, hs, -, hl⟩ := exists_bautinPath_firstLyapunov_eq_zero
  have hs0 : 0 < s := by linarith [hs.1]
  obtain ⟨hb, hp⟩ := bautinPath_meets hs0
  obtain ⟨h3, h2, h1, h0⟩ := bautinPath_coeffs hs0
  refine ⟨bautinPath s, hb, hp, by rw [h3]; positivity, by rw [h1]; positivity,
    by rw [h0]; positivity, by rw [h3, h2, h1, h0]; field_simp; ring,
    bautinPathQ s, bautinPathP s, bautinPath_isCriticalPair hs0, hl⟩

/-! ## Connection conclusions along the path -/

@[tmio M, powerlib_domain] private theorem bautinPath_boundary {s : ℝ} (hs : 0 < s) :
    0 < (bautinPath s).g.coeff3 ∧ 0 < (bautinPath s).g.coeff1 (bautinPath s).Q ∧
      0 < (bautinPath s).g.coeff0 (bautinPath s).Q ∧
      (bautinPath s).g.coeff3 * (bautinPath s).g.coeff2 (bautinPath s).Q *
          (bautinPath s).g.coeff1 (bautinPath s).Q =
        (bautinPath s).g.coeff1 (bautinPath s).Q ^ 2 +
          (bautinPath s).g.coeff3 ^ 2 * (bautinPath s).g.coeff0 (bautinPath s).Q := by
  obtain ⟨h3, h2, h1, h0⟩ := bautinPath_coeffs hs
  rw [h3, h2, h1, h0]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  field_simp
  ring

/-- **The path is supercritical below `s = 2`**: for `0 < s ≤ 2` the boundary point is locally
asymptotically stable (`ℓ₁ < 0`, `mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`). -/
@[tmio TM, powerlib_domain] theorem bautinPath_mem_den_locallyAsymptoticallyStable {s : ℝ}
    (hs : 0 < s) (hs2 : s ≤ 2) :
    connection% (bautinPath s ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨h3, h1, h0, hH⟩ := bautinPath_boundary hs
  have hl : firstLyapunov (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s) < 0 := by
    have h := bautinPath_sign_firstLyapunov hs
    rw [sign_neg (bautinNum_neg hs hs2)] at h
    exact sign_eq_neg_one_iff.mp h
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg (bautinPath s) h3 h1 h0 hH
    (bautinPath_isCriticalPair hs) hl

/-- **The path is subcritical above `s = 21/10`**: for `s ≥ 21/10` the boundary point is unstable
(`ℓ₁ > 0`, `mem_den_unstable_of_firstLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem bautinPath_mem_den_unstable {s : ℝ} (hs : 21 / 10 ≤ s) :
    connection% (bautinPath s ∈ family.den (.flow .unstable)) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨h3, h1, h0, hH⟩ := bautinPath_boundary hs0
  have hl : 0 < firstLyapunov (bautinPath s).field 0 1 (bautinPathQ s) (bautinPathP s) := by
    have h := bautinPath_sign_firstLyapunov hs0
    rw [sign_pos (bautinNum_pos hs)] at h
    exact sign_eq_one_iff.mp h
  exact mem_den_unstable_of_firstLyapunov_pos (bautinPath s) h3 h1 h0 hH
    (bautinPath_isCriticalPair hs0) hl

/-! ## Degenerate points: the second Lyapunov coefficient -/

section Degenerate

open Polynomial Topology Asymptotics Dynamics.CenterManifold
open Dynamics.Degenerate.PlanarFocus (frameX frameY Jet5)

/-- **A degenerate Hopf point with `l₂ < 0` is locally asymptotically stable**: a model on the
Hopf boundary of the quartic (`a₃, a₁, a₀ > 0`, `a₃ a₂ a₁ = a₁² + a₃² a₀`) with a critical pair
`(q, p)`, an approximate centre manifold `φ` of its field (`C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`,
values in `ker critP`, invariance defect `O(‖u‖⁵)` for `A = DF(0)`, `f = F − A`) and the quintic
jet `J` of the chart field of `φ` in the critical chart, with `l₁(J) = 0` and `l₂(J) < 0`
(`Dynamics.CenterManifold.localAsymptoticStable_of_l2_neg_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg
    (m : Model) (h3 : 0 < m.g.coeff3) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) {φ : State 4 → State 4}
    (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, critP q p (φ x) = 0)
    (hdef : IsOrder (critP q p) (invarianceDefect (fderiv ℝ m.field 0) (critP q p)
      (fun x => m.field x - fderiv ℝ m.field 0 x) φ) 5)
    {J : Jet5}
    (hx : (fun u => frameX (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ (critι q) (critπ p) u) -
      (-ω * frameY (rotL ω) ω u + Dynamics.Degenerate.poly3 J.F (frameX u)
        (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY (rotL ω) ω (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ (critι q) (critπ p) u) -
      (ω * frameX u + Dynamics.Degenerate.poly3 J.G (frameX u)
        (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : J.l2 ω < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (m.sq_freq_of_isCriticalPair h3.ne' hcp)
  exact localAsymptoticStable_of_l2_neg_of_charpoly m.contDiff_field hcp hchar hr hφ hφ0 hDφ
    hφP hdef hx hy hl1 hl2

/-- **A degenerate Hopf point with `l₂ > 0` is unstable** (hypotheses as
`mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`, `l₂(J) > 0`;
`Dynamics.CenterManifold.unstable_of_l2_pos_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_secondLyapunov_pos
    (m : Model) (h3 : 0 < m.g.coeff3) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) {φ : State 4 → State 4}
    (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, critP q p (φ x) = 0)
    (hdef : IsOrder (critP q p) (invarianceDefect (fderiv ℝ m.field 0) (critP q p)
      (fun x => m.field x - fderiv ℝ m.field 0 x) φ) 5)
    {J : Jet5}
    (hx : (fun u => frameX (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ (critι q) (critπ p) u) -
      (-ω * frameY (rotL ω) ω u + Dynamics.Degenerate.poly3 J.F (frameX u)
        (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY (rotL ω) ω (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ (critι q) (critπ p) u) -
      (ω * frameX u + Dynamics.Degenerate.poly3 J.G (frameX u)
        (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : 0 < J.l2 ω) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (m.sq_freq_of_isCriticalPair h3.ne' hcp)
  exact unstable_of_l2_pos_of_charpoly m.contDiff_field hcp hchar hr hφ hφ0 hDφ hφP hdef hx hy
    hl1 hl2

end Degenerate

end VSM
end powerlib.GFM.Line
