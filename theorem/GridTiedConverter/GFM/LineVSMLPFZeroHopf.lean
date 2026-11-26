import theorem.GridTiedConverter.GFM.LineVSMLPFFold
import theorem.GridTiedConverter.GFM.HopfLineLPFAngle
import theorem.Dynamics.ZeroHopfReduction

/-! # The VSM with a power filter on a dynamic R–L line: the zero–Hopf points of the fold

Model boundary.
* The five-state VSM + power filter `Line.VSMLPF` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid
  dq frame at `ω₀`, export-positive power, constant `E`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no voltage loop, inner loops, PLL,
  delay or PWM. Read about a selected angle (`Line.VSMLPF.Model`), translated so that the
  operating point is the origin; every operating angle `δ*`.
* The zero–Hopf points of the fold: balanced physical models (`P(δ*) = P_ref`,
  `E, V, L, ω₀, M, D, ω_c > 0`, `R ≥ 0`) at a fold `K = P'(δ*) = 0` (`a₀ = 0`) with `a₁ > 0`
  (`D > D_line`) and `Δ₃ = 0`; off a strict Routh violation (`a₂ < 0`) there
  `det(sI − J) = s (s² + Ω²)(s² + a₄ s + a₃ − Ω²)`, `Ω² = a₂/a₄`: the eigenvalues `0`, `±iΩ` and
  two in the open left half plane. In the atoms of the rotated frame (`c = ω_c`, `d = D/M`,
  `k = Q/M`, `g = E²/(M L)`, `σ = R/L`, `w = ω₀`, `ρ = σ² + w²`) the conditions are the fold
  `g w = k ρ` (so `k > 0`) and the two Hopf relations at `Ω` of
  `theorem/GridTiedConverter/GFM/HopfLineLPFAngle.lean` (with `a₀ = 0`); together they force
  `Ω² < ρ` and `2Ω² < a₃`.
* Level: Lyapunov instability (LeanForControl's `Unstable`) of the operating point, through
  `Line.VSMLPF.family`; exact closed forms of the normal-form coefficients `a`, `b`, `c` are static
  evidence.
* Not decided: the codimension-two fold points `Line.VSMLPF.Model.FoldDegenerate` (the
  Bogdanov–Takens damping `D = D_line` with `a₂ (a₄ a₃ − a₂) = 0`: a triple zero, or a double zero
  with a pair `±i√a₃`), whose centre manifolds are three- and four-dimensional with a nilpotent
  linear part; the library has no normal-form law for them.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.5 and §8.7 (the
zero–Hopf normal form and its projection formulas); the generic law
`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`
(`theorem/Dynamics/ZeroHopfReduction.lean`); the rotated frame and the critical vectors
`Line.VSMLPF.angleRead`, `Line.VSMLPF.Model.critQ`, `Line.VSMLPF.Model.critP`
(`theorem/GridTiedConverter/GFM/HopfLineLPFAngle.lean`) with the pattern `AnglePattern.jac`,
`AnglePattern.bilin`, `Line.VSMLPF.angleVecQ`, `Line.VSMLPF.angleVecP` and the eigenvector laws
`AnglePattern.right`, `AnglePattern.left`
(`theorem/GridTiedConverter/GFM/HopfLineLPFAnglePattern.lean`); the null pair, the fold
coefficient and the characteristic polynomial at a fold `Line.VSMLPF.Model.isNullPair_fold`,
`Line.VSMLPF.Model.foldCoeff_fold`, `Line.VSMLPF.Model.charpoly_fold`
(`theorem/GridTiedConverter/GFM/LineVSMLPFFold.lean`); the second derivative
`Line.VSMLPF.bilinC_field_eq` (`theorem/GridTiedConverter/GFM/HopfLineLPF.lean`). The closed
forms and the certificate of the pairing were derived with exact computer algebra (SymPy,
untrusted discovery) and are proved here by `field_simp` and `linear_combination`.

Results.
* **`Line.VSMLPF.Model.isCriticalPair_crit_zeroHopf`**: at a fold zero–Hopf point
  (`Line.VSMLPF.Model.critQ Ω`, `Line.VSMLPF.Model.critP Ω`) is a critical pair at every
  operating angle; the pairing of the rotated vectors is `⟨p̃, q⟩ = 2Ω² r(iΩ) L(iΩ)`,
  `r(iΩ) = (a₃ − 2Ω²) + i a₄ Ω`, `L(iΩ) = (ρ − Ω²) + 2iσΩ`.
* **The coefficients**: `a = (P(δ*) − c₀)/(2 (D − D_line))` (`Line.VSMLPF.Model.foldCoeff_fold`);
  `Line.VSMLPF.Model.zhB_crit`: `b = ((P(δ*) + c₀) Λ − 2 c₀ ρ (ρ + Ω²))/(2 (D − D_line))`,
  `Λ = (ρ − Ω²)² + 4σ²Ω²` (an identity at every `Ω`); `Line.VSMLPF.Model.zhC_zeroHopf`:
  `c = −(ω_c (P(δ*) − c₀)/M) ((ρ − Ω²)(a₃ − 2Ω²) + 2σ a₄ Ω²)/(2Ω² ((a₃ − 2Ω²)² + a₄² Ω²))`.
* **`Line.VSMLPF.Model.zeroHopfDecided_zeroHopf`**: `c = −λ a` with
  `λ = a₁ ((ρ − Ω²)(a₃ − 2Ω²) + 2σ a₄ Ω²)/(ρ Ω² ((a₃ − 2Ω²)² + a₄² Ω²)) > 0` and `a ≠ 0`, so
  `a(a − c) > 0`: every zero–Hopf point of the fold lies in a decided regime; the regimes
  `ab > 0` and `a = 0 ∧ bc > 0` are not needed (`a ≠ 0` at every fold off `D = D_line`).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSMLPF.family`.
* **`Line.VSMLPF.mem_den_unstable_of_zeroHopf`**: a balanced physical model at a fold `K = 0`
  with `a₁ > 0` and `Δ₃ = 0` is unstable.
* **`Line.VSMLPF.mem_den_unstable_of_fold_of_coeff1_ne`**: a balanced physical model at a fold
  with `a₁ ≠ 0` (off the Bogdanov–Takens damping) is unstable.
* **`Line.VSMLPF.mem_den_unstable_of_fold_of_not_foldDegenerate`**: a balanced physical model at
  a fold off `Line.VSMLPF.Model.FoldDegenerate` is unstable; at a fold the operating point is
  never locally asymptotically stable off the codimension-two points `FoldDegenerate`, which
  need `R > 0` (`Line.VSMLPF.Model.not_foldDegenerate_of_R_eq_zero`: on the lossless line every
  balanced fold point is unstable).
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF
open Complex Matrix Polynomial
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff)
open powerlib.Dynamics.CenterManifold (zhB zhC ZeroHopfDecided)

/-! ## The model in the rotated frames -/

/-- **The Jacobian in the rotated frame**: `J S = S J'` for the reading
`S = Line.VSMLPF.angleRead M (E/L) δ*` and the pattern `J' = AnglePattern.jac`. -/
@[tmio M, powerlib_domain] private theorem zh_jac_read (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (v : Fin 5 → ℂ) :
    jacobianC m.field 0 *ᵥ angleRead m.g.M (m.g.E / m.g.L) m.δ v =
      angleRead m.g.M (m.g.E / m.g.L) m.δ (AnglePattern.jac (m.g.ωc : ℂ)
        ((m.g.D / m.g.M : ℝ) : ℂ) ((m.Q / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
        ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) *ᵥ v) := by
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q := rfl
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hXc : (m.g.X : ℂ) = m.g.ω0 * m.g.L := by simp [Network.X]
  rw [m.jacobianC_field]
  ext k
  fin_cases k <;> simp [angleRead, AnglePattern.jac, Model.jac, jacobian, Matrix.mulVec,
    dotProduct, Fin.sum_univ_five, Linear.complexify, hQ, hXc] <;> field_simp
  all_goals first | ring1 |
    linear_combination (m.g.ωc : ℂ) * (m.g.E : ℂ) ^ 2 * v 3 * Complex.cos_sq_add_sin_sq (m.δ : ℂ)

/-- **The transposed Jacobian in the dual rotated frame**: `Jᵀ S⁻ᵀ = S⁻ᵀ J'ᵀ`,
`S⁻ᵀ = Line.VSMLPF.angleRead M⁻¹ (L/E) δ*`. -/
@[tmio M, powerlib_domain] private theorem zh_jacT_read (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hE : m.g.E ≠ 0) (v : Fin 5 → ℂ) :
    (jacobianC m.field 0)ᵀ *ᵥ angleRead m.g.M⁻¹ (m.g.L / m.g.E) m.δ v =
      angleRead m.g.M⁻¹ (m.g.L / m.g.E) m.δ ((AnglePattern.jac (m.g.ωc : ℂ)
        ((m.g.D / m.g.M : ℝ) : ℂ) ((m.Q / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
        ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ))ᵀ *ᵥ v) := by
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q := rfl
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hEc : (m.g.E : ℂ) ≠ 0 := by exact_mod_cast hE
  have hXc : (m.g.X : ℂ) = m.g.ω0 * m.g.L := by simp [Network.X]
  rw [m.jacobianC_field]
  ext k
  fin_cases k <;> simp [angleRead, AnglePattern.jac, Model.jac, jacobian, Matrix.mulVec,
    dotProduct, Fin.sum_univ_five, Linear.complexify, hQ, hXc] <;> field_simp
  all_goals first | ring1 |
    linear_combination (m.g.M : ℂ) * v 4 * Complex.cos_sq_add_sin_sq (m.δ : ℂ)

/-- The pairing of the two rotated frames: `⟨S⁻ᵀ v, S u⟩ = ⟨v, u⟩`. -/
@[tmio M, powerlib_domain] private theorem zh_star_dot {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (θ : ℝ) (u v : Fin 5 → ℂ) :
    star (angleRead a⁻¹ b⁻¹ θ v) ⬝ᵥ angleRead a b θ u = star v ⬝ᵥ u := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  simp [angleRead, dotProduct, Fin.sum_univ_five, Complex.conj_ofReal, -Complex.ofReal_cos,
    -Complex.ofReal_sin]
  field_simp
  linear_combination (starRingEnd ℂ (v 3) * u 3 + starRingEnd ℂ (v 4) * u 4) * hcs

/-- **The second derivative in the rotated frames**: `⟨S⁻ᵀ p, B(S u, S v)⟩ = ⟨p, B'(u, v)⟩`,
`B' = AnglePattern.bilin` with `N = P(δ*)/M`. -/
@[tmio M, powerlib_domain] private theorem zh_pairing_bilin (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hE : m.g.E ≠ 0) (p u v : Fin 5 → ℂ) :
    pairing (angleRead m.g.M⁻¹ (m.g.L / m.g.E) m.δ p)
        (bilinC m.field 0 (angleRead m.g.M (m.g.E / m.g.L) m.δ u)
          (angleRead m.g.M (m.g.E / m.g.L) m.δ v)) =
      pairing p (AnglePattern.bilin (m.g.ωc : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
        ((m.g.qssPower m.δ / m.g.M : ℝ) : ℂ) u v) := by
  have hH : hess m.field 0 = hess m.g.field m.point := by
    funext k i j
    show iteratedFDeriv ℝ 2 (fun z => m.g.field (z + m.point)) 0 _ _ = _
    simp only [iteratedFDeriv_comp_add_right, zero_add, hess]
  have hB : bilinC m.field 0 = bilinC m.g.field m.point := by unfold bilinC; rw [hH]
  have p0 : m.point 0 = m.δ := by simp [Model.point, qss]
  have p3 : m.point 3 = (m.g.is m.δ).re := by simp [Model.point, qss]
  have p4 : m.point 4 = (m.g.is m.δ).im := by simp [Model.point, qss]
  have hP : m.g.power m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.qssPower m.δ := rfl
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hEc : (m.g.E : ℂ) ≠ 0 := by exact_mod_cast hE
  rw [hB, bilinC_field_eq, p0, p3, p4, hP, pairing_apply, pairing_apply]
  have hcs : (Real.cos m.δ : ℂ) ^ 2 + (Real.sin m.δ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq m.δ
  simp [Fin.sum_univ_five, angleRead, AnglePattern.bilin, Complex.conj_ofReal,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  field_simp
  linear_combination ((m.g.ωc : ℂ) * starRingEnd ℂ (p 2) * (m.g.E : ℂ) ^ 2 *
    (u 0 * v 4 + v 0 * u 4) - (m.g.M : ℂ) * u 0 * v 0 * (m.g.L : ℂ) * starRingEnd ℂ (p 3)) * hcs

@[tmio M, powerlib_domain] private theorem zh_read_smul (a b θ : ℝ) (z : ℂ) (v : Fin 5 → ℂ) :
    angleRead a b θ (z • v) = z • angleRead a b θ v := by
  ext k; fin_cases k <;> simp [angleRead] <;> ring

@[tmio M, powerlib_domain] private theorem zh_star_read (a b θ : ℝ) (v : Fin 5 → ℂ) :
    star (angleRead a b θ v) = angleRead a b θ (star v) := by
  ext k; fin_cases k <;> simp [angleRead, Complex.conj_ofReal, -Complex.ofReal_cos,
    -Complex.ofReal_sin]

/-- **The fold zero–Hopf relations in the atoms** (`c = ω_c`, `d = D/M`, `k = Q/M`,
`g = E²/(M L)`, `σ = R/L`, `w = ω₀`, `ρ = σ² + w²`): the fold `g w = k ρ`, the reduced second
Hopf relation `c k = (d + c)(ρ − Ω²) + 2σ(d c − Ω²)` and the first Hopf relation. -/
@[tmio M, powerlib_domain] private theorem zh_rel {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) {Ω : ℝ} (h1 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0)
    (h2 : m.g.coeff2 m.Q = m.g.coeff4 * Ω ^ 2) :
    m.g.E ^ 2 / (m.g.M * m.g.L) * m.g.ω0 = m.Q / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) ∧
    m.g.ωc * (m.Q / m.g.M) = (m.g.D / m.g.M + m.g.ωc) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 -
      Ω ^ 2) + 2 * (m.g.R / m.g.L) * (m.g.D / m.g.M * m.g.ωc - Ω ^ 2) ∧
    2 * (m.g.R / m.g.L) * m.g.ωc * (m.Q / m.g.M) =
      (m.g.D / m.g.M * m.g.ωc - Ω ^ 2) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - Ω ^ 2) -
        2 * (m.g.R / m.g.L) * (m.g.D / m.g.M + m.g.ωc) * Ω ^ 2 := by
  obtain ⟨c4, c3, c2, c1, c0⟩ := Model.coeff_atoms hp
  have h0 : m.g.coeff0 m.Q = 0 := by
    rw [m.coeff0_eq hp.1.L.ne' hp.1.absSq_pos, hK]; simp
  rw [c0] at h0
  have hF := (mul_eq_zero.mp h0).resolve_left hp.2.2.2.ne'
  refine ⟨by linarith, ?_, ?_⟩
  · rw [c2, c4] at h2; linear_combination -h2
  · rw [c3, c1] at h1; linear_combination -h1

/-- **The pairing of the critical vectors at a fold zero–Hopf point**:
`⟨p̃(−Ω), q⟩ = 2Ω² r(iΩ) L(iΩ)`, `r(iΩ) = (a₃ − 2Ω²) + i a₄ Ω`, `L(iΩ) = (ρ − Ω²) + 2iσΩ`. -/
@[tmio M, powerlib_domain] private theorem zh_pairing_eq {c d K g σ w O : ℂ}
    (hF : g * w = K * (σ ^ 2 + w ^ 2))
    (hK' : c * K = (d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2) :
    angleVecP c d g σ w (-O) I ⬝ᵥ angleVecQ d σ w O I =
      2 * O ^ 2 * ((σ ^ 2 + w ^ 2 + 2 * σ * (d + c) + d * c - 2 * O ^ 2) +
        (c + d + 2 * σ) * O * I) * ((σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * O * I) := by
  have hd : O ^ 4 - O ^ 2 * c * d + 3 * O ^ 2 * σ ^ 2 - O ^ 2 * w ^ 2 - 3 * c * d * σ ^ 2 +
      c * d * w ^ 2 - 2 * c * σ * (σ ^ 2 + w ^ 2) - 2 * d * σ * (σ ^ 2 + w ^ 2) = 0 := by
    linear_combination -hK + 2 * σ * hK'
  simp only [angleVecP, angleVecQ, dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (2 * (O * I + σ) * c) * hF + (2 * (σ ^ 2 + w ^ 2) * (O * I + σ)) * hK' +
    (2 * O ^ 2 * I ^ 2 + O ^ 2 - σ ^ 2 - w ^ 2) * hd +
    (-O ^ 2 * (3 * O ^ 4 * I ^ 4 - 3 * O ^ 4 * I ^ 2 + 5 * O ^ 4 + 2 * O ^ 3 * c * I ^ 3 -
      2 * O ^ 3 * c * I + 2 * O ^ 3 * d * I ^ 3 - 2 * O ^ 3 * d * I + 12 * O ^ 3 * I ^ 3 * σ -
      12 * O ^ 3 * I * σ + O ^ 2 * c * d * I ^ 2 - 3 * O ^ 2 * c * d + 8 * O ^ 2 * c * I ^ 2 * σ -
      4 * O ^ 2 * c * σ + 8 * O ^ 2 * d * I ^ 2 * σ - 4 * O ^ 2 * d * σ +
      18 * O ^ 2 * I ^ 2 * σ ^ 2 + 6 * O ^ 2 * I ^ 2 * w ^ 2 - 4 * O ^ 2 * σ ^ 2 -
      8 * O ^ 2 * w ^ 2 + 4 * O * c * d * I * σ + 12 * O * c * I * σ ^ 2 + 4 * O * c * I * w ^ 2 +
      12 * O * d * I * σ ^ 2 + 4 * O * d * I * w ^ 2 + 12 * O * I * σ ^ 3 +
      12 * O * I * σ * w ^ 2 + 4 * c * d * w ^ 2 + 4 * c * σ ^ 3 + 4 * c * σ * w ^ 2 +
      4 * d * σ ^ 3 + 4 * d * σ * w ^ 2 + 3 * σ ^ 4 + 6 * σ ^ 2 * w ^ 2 + 3 * w ^ 4)) * I_sq

/-- **Positivity at a fold zero–Hopf point** (real atoms, `c, d, K, w, X > 0`, `σ ≥ 0`): the
two Hopf relations force `X < ρ` and `2X < a₃`, `ρ = σ² + w²`,
`a₃ = ρ + 2σ(d + c) + d c`, `X = Ω²`. -/
@[tmio M, powerlib_domain] private theorem zh_pos {c d K σ w X : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hσ : 0 ≤ σ) (hw : 0 < w) (hX : 0 < X) (hK0 : 0 < K)
    (hK' : c * K = (d + c) * (σ ^ 2 + w ^ 2 - X) + 2 * σ * (d * c - X))
    (hK : 2 * σ * c * K = (d * c - X) * (σ ^ 2 + w ^ 2 - X) - 2 * σ * (d + c) * X) :
    X < σ ^ 2 + w ^ 2 ∧ 2 * X < σ ^ 2 + w ^ 2 + 2 * σ * (d + c) + d * c := by
  set ρ := σ ^ 2 + w ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hcK : 0 < c * K := mul_pos hc hK0
  -- `(X − q)(X − ρ + 4σ²) = 2σpρ`, `p = c + d`, `q = d c`
  have hR : (X - d * c) * (X - ρ + 4 * σ ^ 2) = 2 * σ * (c + d) * ρ := by
    linear_combination -hK + 2 * σ * hK'
  have hA : X < ρ := by
    by_contra hn
    push Not at hn
    have h1 : 0 < 2 * σ * (d * c - X) := by
      have : (d + c) * (ρ - X) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (by linarith)
      linarith
    have hσ0 : 0 < σ := by
      rcases hσ.lt_or_eq with h | h
      · exact h
      · rw [← h] at h1; simp at h1
    have hq : X < d * c := by nlinarith
    have : (X - d * c) * (X - ρ + 4 * σ ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by nlinarith)
    have : 0 < 2 * σ * (c + d) * ρ := by positivity
    linarith
  refine ⟨hA, ?_⟩
  by_cases hq : X ≤ d * c
  · nlinarith [mul_nonneg hσ (le_of_lt (add_pos hd hc))]
  push Not at hq
  exfalso
  have hσ0 : 0 < σ := by
    rcases hσ.lt_or_eq with h | h
    · exact h
    · rw [← h] at hR
      have : (X - d * c) * (X - ρ) = 0 := by linear_combination hR
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
  -- `2σρ · cK > 0` with `2σρ (c + d) = (X − q)(X − ρ + 4σ²)/1` gives `−(ρ − X)² − 4σ²X > 0`
  have h1 : 0 < 2 * σ * ρ * (c * K) := by positivity
  have h2 : 2 * σ * ρ * (c * K) = (X - d * c) * ((X - ρ + 4 * σ ^ 2) * (ρ - X) -
      4 * σ ^ 2 * ρ) := by
    rw [hK']; linear_combination (X - ρ) * hR
  have h3 : (X - ρ + 4 * σ ^ 2) * (ρ - X) - 4 * σ ^ 2 * ρ < 0 := by nlinarith
  have : (X - d * c) * ((X - ρ + 4 * σ ^ 2) * (ρ - X) - 4 * σ ^ 2 * ρ) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) h3
  linarith

/-! ## The critical pair at the fold zero–Hopf points -/

/-- The data of a fold zero–Hopf point in the atoms, with their signs. -/
@[tmio M, powerlib_domain] private theorem zh_data {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) {Ω : ℝ} (hΩ : 0 < Ω) (h1 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0)
    (h2 : m.g.coeff2 m.Q = m.g.coeff4 * Ω ^ 2) :
    0 < m.Q / m.g.M ∧ Ω ^ 2 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 ∧
      2 * Ω ^ 2 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 + 2 * (m.g.R / m.g.L) *
        (m.g.D / m.g.M + m.g.ωc) + m.g.D / m.g.M * m.g.ωc := by
  obtain ⟨hF, hK', hKr⟩ := zh_rel hp hK h1 h2
  obtain ⟨hN, hM, hD, hc⟩ := hp
  have hσ : 0 ≤ m.g.R / m.g.L := div_nonneg hN.R hN.L.le
  have hg : 0 < m.g.E ^ 2 / (m.g.M * m.g.L) * m.g.ω0 := by
    have := hN.E; have := hN.L; have := hN.ω0; positivity
  have hρ : 0 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 := by have := hN.ω0; positivity
  have hK0 : 0 < m.Q / m.g.M := by
    rw [hF] at hg
    exact (pos_iff_pos_of_mul_pos hg).mpr hρ
  obtain ⟨hA, hB⟩ := zh_pos hc (div_pos hD hM) hσ hN.ω0 (pow_pos hΩ 2) hK0
    (by linear_combination hK') (by linear_combination hKr)
  exact ⟨hK0, hA, by linarith⟩

/-- **The critical pair at the fold zero–Hopf points**: for a balanced physical model at a fold
`K = 0` with `Ω⁴ − a₃ Ω² + a₁ = 0` and `a₂ = a₄ Ω²` (`Ω > 0`: the eigenvalues `0`, `±iΩ`),
(`Line.VSMLPF.Model.critQ Ω`, `Line.VSMLPF.Model.critP Ω`) is a critical pair at every operating
angle: the rotated pattern of `theorem/GridTiedConverter/GFM/HopfLineLPFAnglePattern.lean`
satisfies its two Hopf relations there (`a₀ = 0`), and the pairing is
`⟨p̃, q⟩ = 2Ω² r(iΩ) L(iΩ) ≠ 0`, `r(iΩ) = (a₃ − 2Ω²) + i a₄ Ω`, `L(iΩ) = (ρ − Ω²) + 2iσΩ`
(`Ω² < ρ`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isCriticalPair_crit_zeroHopf {m : Model}
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0) {Ω : ℝ} (hΩ : 0 < Ω)
    (h1 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0)
    (h2 : m.g.coeff2 m.Q = m.g.coeff4 * Ω ^ 2) :
    IsCriticalPair m.field 0 Ω (m.critQ Ω) (m.critP Ω) := by
  obtain ⟨hF, hK', hKr⟩ := zh_rel hp hK h1 h2
  obtain ⟨-, hA, hB⟩ := zh_data hp hK hΩ h1 h2
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  have hFc : ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) * (m.g.ω0 : ℂ) =
      ((m.Q / m.g.M : ℝ) : ℂ) * (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2) := by
    exact_mod_cast hF
  have hK'c : (m.g.ωc : ℂ) * ((m.Q / m.g.M : ℝ) : ℂ) = (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) *
      (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) +
      2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - (Ω : ℂ) ^ 2) := by
    exact_mod_cast hK'
  have hKc : 2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (m.g.ωc : ℂ) * ((m.Q / m.g.M : ℝ) : ℂ) =
      (((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - (Ω : ℂ) ^ 2) *
        (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) -
      2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) * (Ω : ℂ) ^ 2 := by
    exact_mod_cast hKr
  have hRc : (m.g.ωc : ℂ) * ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) * (m.g.ω0 : ℂ) =
      (m.g.ωc : ℂ) * ((m.Q / m.g.M : ℝ) : ℂ) *
        (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) +
      (Ω : ℂ) ^ 2 * ((((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) *
        (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) +
        2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - (Ω : ℂ) ^ 2)) := by
    linear_combination (m.g.ωc : ℂ) * hFc + (Ω : ℂ) ^ 2 * hK'c
  have hz := zh_pairing_eq hFc hK'c hKc
  have hc0 : angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
      ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (-(Ω : ℂ))
        I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (Ω : ℂ)
          I ≠ 0 := by
    rw [hz]
    have hr : (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 +
        2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) +
        ((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - 2 * (Ω : ℂ) ^ 2) +
        ((m.g.ωc : ℂ) + ((m.g.D / m.g.M : ℝ) : ℂ) + 2 * ((m.g.R / m.g.L : ℝ) : ℂ)) * (Ω : ℂ) * I ≠
          0 := by
      have e : (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 +
          2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) +
          ((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - 2 * (Ω : ℂ) ^ 2) +
          ((m.g.ωc : ℂ) + ((m.g.D / m.g.M : ℝ) : ℂ) + 2 * ((m.g.R / m.g.L : ℝ) : ℂ)) * (Ω : ℂ) * I =
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 + 2 * (m.g.R / m.g.L) * (m.g.D / m.g.M + m.g.ωc) +
            m.g.D / m.g.M * m.g.ωc - 2 * Ω ^ 2 : ℝ) : ℂ) +
          (((m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) * Ω : ℝ) : ℂ) * I := by push_cast; ring
      rw [e]
      have : 0 < (m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) * Ω := by
        have := hp.2.2.2; have := div_pos hp.2.2.1 hp.2.1
        have := div_nonneg hp.1.R hp.1.L.le; positivity
      intro h
      have h' := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, Complex.zero_im, mul_zero, mul_one, zero_add, add_zero] at h'
      exact this.ne' h'
    have hLc : (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) +
        2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (Ω : ℂ) * I ≠ 0 := by
      have e : (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) +
          2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (Ω : ℂ) * I =
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - Ω ^ 2 : ℝ) : ℂ) +
            ((2 * (m.g.R / m.g.L) * Ω : ℝ) : ℂ) * I := by push_cast; ring
      rw [e]
      refine Complex.ne_zero_of_re_pos ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      linarith
    have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hΩc)) hr) hLc
  have hf : m.field 0 = 0 := by
    have h' := (m.field_point_eq_zero_iff hM hp.2.2.2.ne' hL hp.1.absSq_pos.ne').mpr hb
    simpa [Model.field] using h'
  refine ⟨hf, hΩ, ?_, ?_, ?_⟩
  · unfold Model.critQ
    rw [zh_jac_read m hM hL, AnglePattern.right I_sq hKc hRc, zh_read_smul]
  · unfold Model.critP
    rw [zh_jacT_read m hM hL hE, Matrix.mulVec_smul, AnglePattern.left I_sq hKc hRc, smul_comm,
      zh_read_smul, zh_read_smul]
  · unfold Model.critP Model.critQ
    rw [show m.g.L / m.g.E = (m.g.E / m.g.L)⁻¹ from (inv_div _ _).symm,
      zh_star_dot hM (div_ne_zero hE hL)]
    have hstar : star ((starRingEnd ℂ (angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ)
          (-(Ω : ℂ)) I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
            (m.g.ω0 : ℂ) (Ω : ℂ) I))⁻¹ • angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (Ω : ℂ)
          I) =
        (angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
          ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ)
            (-(Ω : ℂ)) I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
              (m.g.ω0 : ℂ) (Ω : ℂ) I)⁻¹ • star (angleVecP (m.g.ωc : ℂ)
          ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
            ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (Ω : ℂ) I) := by
      ext k
      simp [Pi.star_apply]
    rw [hstar, smul_dotProduct, star_angleVecP, smul_eq_mul, inv_mul_cancel₀ hc0]

/-! ## The coefficients -/

/-- The tangent of the fold in the rotated frame: `q₀ = (1, 0, 0, w/ρ, σ/ρ)`. -/
@[tmio M, powerlib_domain] private theorem zh_tangent_read {m : Model} (hp : Meets m .physical) :
    toC (WithLp.toLp 2 m.btTangent) = angleRead m.g.M (m.g.E / m.g.L) m.δ
      ![1, 0, 0, ((m.g.ω0 / ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) : ℝ) : ℂ),
        ((m.g.R / m.g.L / ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) : ℝ) : ℂ)] := by
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos.ne'
  have hw := hp.1.ω0
  have hρ : (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 ≠ 0 := by positivity
  have hρ' : m.g.R ^ 2 + m.g.ω0 ^ 2 * m.g.L ^ 2 ≠ 0 := by
    have : m.g.absSq = m.g.R ^ 2 + m.g.ω0 ^ 2 * m.g.L ^ 2 := by
      simp only [Network.absSq, Network.X]; ring
    rw [← this]; exact hZ
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hρc : (m.g.ω0 : ℂ) ^ 2 * (m.g.L : ℂ) ^ 2 + (m.g.R : ℂ) ^ 2 ≠ 0 := by
    have : m.g.ω0 ^ 2 * m.g.L ^ 2 + m.g.R ^ 2 ≠ 0 := by rw [add_comm]; exact hρ'
    exact_mod_cast this
  have hρc' : ((m.g.R : ℂ) / m.g.L) ^ 2 + (m.g.ω0 : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hρ
  rw [Model.btTangent_eq]
  ext k
  fin_cases k <;> simp [toC, angleRead, Network.absSq, Network.X, -Complex.ofReal_cos,
    -Complex.ofReal_sin] <;> field_simp

/-- The left null vector of the fold in the dual rotated frame:
`p₀ = (D, M, −M/ω_c, −c₀, −κ)/(D − D_line)`, `κ = E² X/|Z|²`. -/
@[tmio M, powerlib_domain] private theorem zh_foldP_read {m : Model} (hp : Meets m .physical)
    (hD : m.g.D ≠ m.g.Dline) :
    toC (WithLp.toLp 2 m.foldP) = angleRead m.g.M⁻¹ (m.g.L / m.g.E) m.δ
      ((((m.g.D - m.g.Dline)⁻¹ : ℝ) : ℂ) • ![(m.g.D : ℂ), (m.g.M : ℂ),
        ((-(m.g.M / m.g.ωc) : ℝ) : ℂ), ((-m.g.c0 : ℝ) : ℂ), ((-m.g.κ : ℝ) : ℂ)]) := by
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos.ne'
  have hE := hp.1.E.ne'
  have hM := hp.2.1.ne'
  have hω := hp.2.2.2.ne'
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hDc : (m.g.D : ℂ) - m.g.Dline ≠ 0 := by
    have : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
    exact_mod_cast this
  ext k
  fin_cases k <;> simp [toC, angleRead, Model.foldP, Network.c0, Network.κ, -Complex.ofReal_cos,
    -Complex.ofReal_sin] <;> push_cast <;> field_simp <;> ring

/-- The pattern of `b`: `⟨p, B(q, q̄)⟩` along the critical vector of the rotated frame. -/
@[tmio M, powerlib_domain] private theorem zh_b_pattern (c d g N σ w O : ℂ) (p : Fin 5 → ℂ) :
    pairing p (AnglePattern.bilin c g N (angleVecQ d σ w O I) (angleVecQ d σ w (-O) I)) =
      starRingEnd ℂ (p 2) * (c * (g * (2 * σ * (σ ^ 2 + w ^ 2 + O ^ 2)) -
        N * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2))) -
        starRingEnd ℂ (p 3) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) := by
  simp only [pairing_apply, Fin.sum_univ_five, AnglePattern.bilin, angleVecQ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (starRingEnd ℂ (p 2) * c * g * (-2 * O ^ 2 * σ) -
    (starRingEnd ℂ (p 2) * c * N + starRingEnd ℂ (p 3)) *
      (O ^ 2 * (O ^ 2 * I ^ 2 - O ^ 2 - 2 * σ ^ 2 + 2 * w ^ 2))) * I_sq

/-- **The coefficient `b` along the critical vector**: for a physical model, at every `Ω`,
Kuznetsov's `b = ½⟨p₀, B(q, q̄)⟩` of the left null vector `p₀ = Line.VSMLPF.Model.foldP` and
`q = Line.VSMLPF.Model.critQ Ω` is
`b = ((P(δ*) + c₀) Λ − 2 c₀ ρ (ρ + Ω²))/(2 (D − D_line))`, `Λ = (ρ − Ω²)² + 4σ²Ω² = |L(iΩ)|²`,
`c₀ = E² R/|Z|²`, `σ = R/L`, `ρ = σ² + ω₀²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.zhB_crit {m : Model} (hp : Meets m .physical)
    (hD : m.g.D ≠ m.g.Dline) (Ω : ℝ) :
    zhB m.field (WithLp.toLp 2 m.foldP) (m.critQ Ω) =
      ((m.g.qssPower m.δ + m.g.c0) * ((m.g.ρ - Ω ^ 2) ^ 2 + 4 * m.g.σ ^ 2 * Ω ^ 2) -
        2 * m.g.c0 * m.g.ρ * (m.g.ρ + Ω ^ 2)) / (2 * (m.g.D - m.g.Dline)) := by
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  have hω := hp.2.2.2.ne'
  have hZ := hp.1.absSq_pos.ne'
  rw [Dynamics.CenterManifold.zhB_eq_pairing, zh_foldP_read hp hD, Model.critQ, zh_star_read,
    star_angleVecQ, zh_pairing_bilin m hM hL hE, zh_b_pattern]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, map_mul, Complex.conj_ofReal]
  norm_cast
  have hDD : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
  have hZ' : m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 ≠ 0 := hZ
  have hZ'' : m.g.R ^ 2 + m.g.L ^ 2 * m.g.ω0 ^ 2 ≠ 0 := by
    intro h; apply hZ'; linear_combination h
  simp only [Network.ρ, Network.σ, Network.X, Network.c0, Network.absSq]
  field_simp
  ring

/-- The pattern of `c`: `⟨p̃(−Ω), B(q₀, q)⟩ = c L² (g b − N)` along the tangent
`q₀ = (1, 0, 0, a, b)` and the critical vector `q`, `L = (σ + iΩ)² + w²`. -/
@[tmio M, powerlib_domain] private theorem zh_c_pattern (c d g N σ w O a b : ℂ) :
    angleVecP c d g σ w (-O) I ⬝ᵥ AnglePattern.bilin c g N ![1, 0, 0, a, b]
        (angleVecQ d σ w O I) = c * ((σ + O * I) ^ 2 + w ^ 2) ^ 2 * (g * b - N) := by
  simp only [angleVecP, angleVecQ, AnglePattern.bilin, dotProduct, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The coefficient `c` at the fold zero–Hopf points**: for a physical model at a fold `K = 0`
with `Ω > 0`, `Ω⁴ − a₃ Ω² + a₁ = 0` and `a₂ = a₄ Ω²`, Kuznetsov's `c = Re⟨p, B(q₀, q)⟩` of the
tangent `q₀ = Line.VSMLPF.Model.btTangent` and the critical pair `Line.VSMLPF.Model.critQ Ω`,
`Line.VSMLPF.Model.critP Ω` is
`c = −(ω_c (P(δ*) − c₀)/M) ((ρ − Ω²)(a₃ − 2Ω²) + 2σ a₄ Ω²) / (2Ω² ((a₃ − 2Ω²)² + a₄² Ω²))`,
i.e. `−(ω_c (P(δ*) − c₀)/(2MΩ²)) Re(L(iΩ)/r(iΩ))`, `L(s) = (s + σ)² + ω₀²`,
`r(s) = s² + a₄ s + (a₃ − Ω²)` the quadratic cofactor of the quartic. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.zhC_zeroHopf {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) {Ω : ℝ} (hΩ : 0 < Ω) (h1 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0)
    (h2 : m.g.coeff2 m.Q = m.g.coeff4 * Ω ^ 2) :
    zhC m.field (WithLp.toLp 2 m.btTangent) (m.critQ Ω) (m.critP Ω) =
      -(m.g.ωc * (m.g.qssPower m.δ - m.g.c0) / m.g.M) *
        ((m.g.ρ - Ω ^ 2) * (m.g.coeff3 - 2 * Ω ^ 2) + 2 * m.g.σ * m.g.coeff4 * Ω ^ 2) /
        (2 * Ω ^ 2 * ((m.g.coeff3 - 2 * Ω ^ 2) ^ 2 + m.g.coeff4 ^ 2 * Ω ^ 2)) := by
  obtain ⟨hF, hK', hKr⟩ := zh_rel hp hK h1 h2
  obtain ⟨-, hA, hB⟩ := zh_data hp hK hΩ h1 h2
  obtain ⟨c4, c3, -, -, -⟩ := Model.coeff_atoms hp
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  have hZ := hp.1.absSq_pos.ne'
  have hFc : ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) * (m.g.ω0 : ℂ) =
      ((m.Q / m.g.M : ℝ) : ℂ) * (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2) := by
    exact_mod_cast hF
  have hK'c : (m.g.ωc : ℂ) * ((m.Q / m.g.M : ℝ) : ℂ) = (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) *
      (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) +
      2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - (Ω : ℂ) ^ 2) := by
    exact_mod_cast hK'
  have hKc : 2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (m.g.ωc : ℂ) * ((m.Q / m.g.M : ℝ) : ℂ) =
      (((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - (Ω : ℂ) ^ 2) *
        (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (Ω : ℂ) ^ 2) -
      2 * ((m.g.R / m.g.L : ℝ) : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) * (Ω : ℂ) ^ 2 := by
    exact_mod_cast hKr
  have hz := zh_pairing_eq hFc hK'c hKc
  have hpair : ∀ (z : ℂ) (v : Fin 5 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (Ω : ℂ) I)
        v = z⁻¹ * (angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
          ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ)
            (-(Ω : ℂ)) I ⬝ᵥ v) := by
    intro z v
    rw [← star_angleVecP, ← pairing_eq_dotProduct]
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [Dynamics.CenterManifold.zhC_eq_pairing, zh_tangent_read hp, Model.critQ, Model.critP,
    zh_pairing_bilin m hM hL hE, hpair, zh_c_pattern, hz]
  -- the quotient in real atoms
  set σ := m.g.R / m.g.L with hσ
  set w := m.g.ω0 with hw
  set ρ' := σ ^ 2 + w ^ 2 with hρ'
  have hρ : m.g.ρ = ρ' := by
    rw [hρ', hσ, hw, Network.ρ, Network.σ]; congr 1; simp only [Network.X]; field_simp
  have hs : m.g.σ = σ := rfl
  rw [hρ, hs, c4, c3]
  set β := ρ' + 2 * σ * (m.g.D / m.g.M + m.g.ωc) + m.g.D / m.g.M * m.g.ωc - 2 * Ω ^ 2 with hβ
  set γ := (m.g.ωc + m.g.D / m.g.M + 2 * σ) * Ω with hγ
  have eL : (((σ : ℂ) + (Ω : ℂ) * I) ^ 2 + (w : ℂ) ^ 2) =
      ((ρ' - Ω ^ 2 : ℝ) : ℂ) + ((2 * σ * Ω : ℝ) : ℂ) * I := by
    rw [hρ']; push_cast; linear_combination (Ω : ℂ) ^ 2 * I_sq
  have er : ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 + 2 * (σ : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) +
      ((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - 2 * (Ω : ℂ) ^ 2) +
      ((m.g.ωc : ℂ) + ((m.g.D / m.g.M : ℝ) : ℂ) + 2 * (σ : ℂ)) * (Ω : ℂ) * I =
      (β : ℂ) + (γ : ℂ) * I := by
    rw [hβ, hγ, hρ']; push_cast; ring
  have eL' : ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (Ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (Ω : ℂ) * I =
      ((ρ' - Ω ^ 2 : ℝ) : ℂ) + ((2 * σ * Ω : ℝ) : ℂ) * I := by
    rw [hρ']; push_cast; ring
  rw [eL, er, eL']
  have hLne : ((ρ' - Ω ^ 2 : ℝ) : ℂ) + ((2 * σ * Ω : ℝ) : ℂ) * I ≠ 0 := by
    refine Complex.ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rw [hρ']; linarith
  have hγ0 : 0 < γ := by
    have := hp.2.2.2; have := div_pos hp.2.2.1 hp.2.1
    have := div_nonneg hp.1.R hp.1.L.le; rw [hγ]; positivity
  have hrne : (β : ℂ) + (γ : ℂ) * I ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, Complex.zero_im, mul_zero, mul_one, zero_add, add_zero] at h'
    exact hγ0.ne' h'
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hq : (2 * (Ω : ℂ) ^ 2 * ((β : ℂ) + (γ : ℂ) * I) *
      (((ρ' - Ω ^ 2 : ℝ) : ℂ) + ((2 * σ * Ω : ℝ) : ℂ) * I))⁻¹ *
      ((m.g.ωc : ℂ) * (((ρ' - Ω ^ 2 : ℝ) : ℂ) + ((2 * σ * Ω : ℝ) : ℂ) * I) ^ 2 *
        (((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) * ((σ / ρ' : ℝ) : ℂ) -
          ((m.g.qssPower m.δ / m.g.M : ℝ) : ℂ))) =
      ((m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L) * (σ / ρ') - m.g.qssPower m.δ / m.g.M) /
        (2 * Ω ^ 2) : ℝ) : ℂ) * ((((ρ' - Ω ^ 2 : ℝ) : ℂ) + ((2 * σ * Ω : ℝ) : ℂ) * I) /
          ((β : ℂ) + (γ : ℂ) * I)) := by
    push_cast
    field_simp
  rw [hq, Complex.re_ofReal_mul, Complex.div_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, zero_add, add_zero,
    mul_one]
  have hρ0 : 0 < ρ' := by have := hp.1.ω0; rw [hρ']; positivity
  have hRσ : m.g.R = σ * m.g.L := by rw [hσ]; field_simp
  have habs : m.g.absSq = m.g.L ^ 2 * ρ' := by
    rw [hρ', hσ, hw, Network.absSq, Network.X]; field_simp
  have hβγ : 0 < β ^ 2 + γ ^ 2 := by positivity
  rw [Network.c0, habs, hRσ]
  have hγ' : (m.g.ωc + m.g.D / m.g.M + 2 * σ) ^ 2 * Ω ^ 2 = γ ^ 2 := by rw [hγ]; ring
  have hγ'' : 2 * σ * (m.g.ωc + m.g.D / m.g.M + 2 * σ) * Ω ^ 2 = 2 * σ * Ω * γ := by
    rw [hγ]; ring
  rw [hγ', hγ'']
  field_simp
  ring

/-- **Every fold zero–Hopf point is in the decided regime `a(a − c) > 0`**: for a physical model
at a fold `K = 0` with `Ω > 0`, `Ω⁴ − a₃ Ω² + a₁ = 0` and `a₂ = a₄ Ω²`, the coefficients
`a = Line.VSMLPF.Model.foldCoeff_fold` and `c = Line.VSMLPF.Model.zhC_zeroHopf` satisfy `c = −λ a`,
`λ = a₁ ((ρ − Ω²)(a₃ − 2Ω²) + 2σ a₄ Ω²)/(ρ Ω² ((a₃ − 2Ω²)² + a₄² Ω²)) > 0` (the Hopf relations
force `Ω² < ρ` and `2Ω² < a₃`, hence `a₁ = Ω² (a₃ − Ω²) > 0` and `D ≠ D_line`), and `a ≠ 0`, so
`a(a − c) = (1 + λ) a² > 0`: `ZeroHopfDecided a b c` for every `b`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.zeroHopfDecided_zeroHopf {m : Model}
    (hp : Meets m .physical) (hK : m.K = 0) {Ω : ℝ} (hΩ : 0 < Ω)
    (h1 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0)
    (h2 : m.g.coeff2 m.Q = m.g.coeff4 * Ω ^ 2) (b : ℝ) :
    ZeroHopfDecided (foldCoeff m.field 0 (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.foldP)) b
      (zhC m.field (WithLp.toLp 2 m.btTangent) (m.critQ Ω) (m.critP Ω)) := by
  obtain ⟨-, hA, hB⟩ := zh_data hp hK hΩ h1 h2
  obtain ⟨c4, c3, -, -, -⟩ := Model.coeff_atoms hp
  have hM := hp.2.1
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have hXL : m.g.X / m.g.L = m.g.ω0 := by simp only [Network.X]; field_simp
  have hρ : m.g.ρ = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 := by rw [Network.ρ, hXL, Network.σ]
  have hσ : m.g.σ = m.g.R / m.g.L := rfl
  have hσ0 : 0 ≤ m.g.R / m.g.L := div_nonneg hp.1.R hp.1.L.le
  have hρ0 : 0 < m.g.ρ := by rw [hρ]; have := hp.1.ω0; positivity
  have h4 : 0 < m.g.coeff4 := by
    rw [c4]; have := hp.2.2.2; have := div_pos hp.2.2.1 hM; positivity
  have hβ : 0 < m.g.coeff3 - 2 * Ω ^ 2 := by rw [c3]; linarith
  have hgap : 0 < m.g.ρ - Ω ^ 2 := by rw [hρ]; linarith
  have h1p : 0 < m.g.coeff1 m.Q := by nlinarith [pow_pos hΩ 2]
  have h1f := m.coeff1_fold hL hZ hK
  have hD : m.g.D ≠ m.g.Dline := by
    intro h; rw [h1f, h, sub_self] at h1p; simp at h1p
  set S := (m.g.ρ - Ω ^ 2) * (m.g.coeff3 - 2 * Ω ^ 2) + 2 * m.g.σ * m.g.coeff4 * Ω ^ 2 with hS
  have hS0 : 0 < S := by
    rw [hS, hσ]
    have : 0 ≤ 2 * (m.g.R / m.g.L) * m.g.coeff4 * Ω ^ 2 := by positivity
    nlinarith [mul_pos hgap hβ]
  set W := (m.g.coeff3 - 2 * Ω ^ 2) ^ 2 + m.g.coeff4 ^ 2 * Ω ^ 2 with hW
  have hW0 : 0 < W := by positivity
  set lam := m.g.coeff1 m.Q * S / (m.g.ρ * Ω ^ 2 * W) with hlam
  have hlam0 : 0 < lam := by positivity
  set a := foldCoeff m.field 0 (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.foldP) with ha
  have hae : a = (m.g.qssPower m.δ - m.g.c0) / (2 * (m.g.D - m.g.Dline)) :=
    m.foldCoeff_fold hp.2.2.2.ne' hL hZ hD
  have ha0 : a ≠ 0 := m.foldCoeff_fold_ne_zero hp hK hD
  have hc : zhC m.field (WithLp.toLp 2 m.btTangent) (m.critQ Ω) (m.critP Ω) = -lam * a := by
    rw [m.zhC_zeroHopf hp hK hΩ h1 h2, hae, hlam, h1f, ← hS, ← hW]
    have hDD : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
    have hΩ0 : Ω ≠ 0 := hΩ.ne'
    field_simp
  refine Or.inr (Or.inl ?_)
  rw [hc]
  have : a * (a - -lam * a) = a ^ 2 * (1 + lam) := by ring
  rw [this]
  have : 0 < a ^ 2 := by positivity
  positivity

/-! ## Instability -/

/-- **The fold zero–Hopf points are unstable**
(`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`): a balanced physical model at a fold
`K = 0` with `a₁ > 0` and `Δ₃ = 0` is unstable. Either `a₂ < 0` (a strict quintic Routh
violation, `Line.VSMLPF.mem_den_unstable`), or `a₂ > 0` and `det(sI − J) = s (s² + Ω²)
(s² + a₄ s + a₃ − Ω²)`, `Ω² = a₂/a₄`, with a Hurwitz quadratic cofactor: a zero–Hopf point,
where `a(a − c) > 0` (`Line.VSMLPF.Model.zeroHopfDecided_zeroHopf`) at the null pair
`Line.VSMLPF.Model.isNullPair_fold` and the critical pair
`Line.VSMLPF.Model.isCriticalPair_crit_zeroHopf`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_zeroHopf (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0) (h1 : 0 < m.g.coeff1 m.Q)
    (h3 : Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hv : m.RouthViolation
  · exact mem_den_unstable m hp hb hv
  have hv' := hv
  unfold Model.RouthViolation Criteria.QuinticRouthViolation at hv'
  push Not at hv'
  obtain ⟨-, -, v2, -, -, -, -, -⟩ := hv'
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have hM := hp.2.1
  obtain ⟨c4, -, -, -, -⟩ := Model.coeff_atoms hp
  have h4 : 0 < m.g.coeff4 := by
    rw [c4]; have := hp.2.2.2; have := div_pos hp.2.2.1 hM
    have := div_nonneg hp.1.R hp.1.L.le; positivity
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  rw [h0] at h3
  unfold Criteria.quinticHurwitzDet3 Criteria.quinticHurwitzDet2 at h3
  have h2 : 0 < m.g.coeff2 m.Q := by
    rcases v2.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at h3
      nlinarith [mul_pos (pow_pos h4 2) h1]
  set Ω := Real.sqrt (m.g.coeff2 m.Q / m.g.coeff4) with hΩdef
  have hΩ : 0 < Ω := Real.sqrt_pos.mpr (div_pos h2 h4)
  have hΩ2 : Ω ^ 2 = m.g.coeff2 m.Q / m.g.coeff4 := Real.sq_sqrt (div_pos h2 h4).le
  have e2 : m.g.coeff2 m.Q = m.g.coeff4 * Ω ^ 2 := by rw [hΩ2]; field_simp
  have e1 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0 := by
    have : m.g.coeff4 ^ 2 * (Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q) = 0 := by
      have e : m.g.coeff4 ^ 2 * Ω ^ 4 = m.g.coeff2 m.Q ^ 2 := by rw [e2]; ring
      linear_combination e - h3 + m.g.coeff4 * m.g.coeff3 * e2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 h4.ne')
  have hcp := m.isCriticalPair_crit_zeroHopf hp hb hK hΩ e1 e2
  have h1f := m.coeff1_fold hL hZ hK
  have hD : m.g.D ≠ m.g.Dline := by
    intro h; rw [h1f, h, sub_self] at h1; simp at h1
  have hm : 0 < m.g.coeff3 - Ω ^ 2 := by
    have : Ω ^ 2 * (m.g.coeff3 - Ω ^ 2) = m.g.coeff1 m.Q := by linear_combination -e1
    have := (pos_iff_pos_of_mul_pos (this ▸ h1)).mp (pow_pos hΩ 2)
    exact this
  have hchar : (jacobianC m.field 0).charpoly = X * (X ^ 2 + C ((Ω : ℂ) ^ 2)) *
      (X ^ 2 + C ((m.g.coeff4 : ℝ) : ℂ) * X + C (((m.g.coeff3 - Ω ^ 2 : ℝ)) : ℂ)) := by
    rw [m.charpoly_fold hL hZ hK, e2,
      show m.g.coeff1 m.Q = Ω ^ 2 * (m.g.coeff3 - Ω ^ 2) by linear_combination e1]
    simp only [map_mul, map_pow, map_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sub]
    ring
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hM.ne' hp.2.2.2.ne' hL hZ.ne').mpr hb
  refine Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly hF hF0
    (m.isNullPair_fold hp hK hD) (Dynamics.CenterManifold.IsCriticalPair.isCritical hcp rfl)
    hchar (fun s hs => ?_) (m.zeroHopfDecided_zeroHopf hp hK hΩ e1 e2 _)
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs
  exact (Criteria.quadratic_roots_re_neg_iff _ _).mpr ⟨h4, hm⟩ s hs

/-- **The fold decided off the Bogdanov–Takens damping**: a balanced physical model at a fold
`K = 0` with `a₁ ≠ 0` (`D ≠ D_line`) is unstable: `Δ₃ ≠ 0`
(`Line.VSMLPF.mem_den_unstable_of_fold_of_ne`), `a₁ < 0` (a strict quintic Routh violation,
`Line.VSMLPF.mem_den_unstable`) or `a₁ > 0`, `Δ₃ = 0` (the zero–Hopf points,
`Line.VSMLPF.mem_den_unstable_of_zeroHopf`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_coeff1_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h1 : m.g.coeff1 m.Q ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases h3 : Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
      (m.g.coeff1 m.Q) (m.g.coeff0 m.Q) = 0
  · rcases h1.lt_or_gt with h | h
    · exact mem_den_unstable m hp hb (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact mem_den_unstable_of_zeroHopf m hp hb hK h h3
  · exact mem_den_unstable_of_fold_of_ne m hp hb hK h1 h3

/-- **The fold decided off its codimension-two points**: a balanced physical model at a fold
`K = 0` off `Line.VSMLPF.Model.FoldDegenerate` is unstable: off the Bogdanov–Takens damping
(`a₁ ≠ 0`) by `Line.VSMLPF.mem_den_unstable_of_fold_of_coeff1_ne`; at it (`a₁ = 0`,
`D = D_line`) `Δ₃ = a₂ (a₄ a₃ − a₂) ≠ 0` and `Line.VSMLPF.mem_den_unstable_of_fold_of_det3_ne`.
Hence at a fold the operating point is never locally asymptotically stable off
`Line.VSMLPF.Model.FoldDegenerate`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_not_foldDegenerate (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (hd : ¬ m.FoldDegenerate) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases h1 : m.g.coeff1 m.Q = 0
  swap
  · exact mem_den_unstable_of_fold_of_coeff1_ne m hp hb hK h1
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (pow_pos hp.1.L 2)
  have hD : m.g.D = m.g.Dline := by
    rw [m.coeff1_fold hL hZ hK] at h1
    have h' : m.g.ρ * (m.g.D - m.g.Dline) / m.g.M = 0 :=
      (mul_eq_zero.mp h1).resolve_left hp.2.2.2.ne'
    rw [div_eq_zero_iff, or_iff_left hp.2.1.ne'] at h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hρ.ne')
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  refine mem_den_unstable_of_fold_of_det3_ne m hp hb hK ?_
  intro h3
  apply hd
  refine ⟨hb, hK, hD, ?_⟩
  rw [h0, h1] at h3
  unfold Criteria.quinticHurwitzDet3 Criteria.quinticHurwitzDet2 at h3
  linear_combination h3

/-- **The lossless line has no degenerate fold points**: for a physical model with `R = 0` the
Bogdanov–Takens damping is `D_line = 0 < D`, so `Line.VSMLPF.Model.FoldDegenerate` fails and
every balanced fold point is unstable
(`Line.VSMLPF.mem_den_unstable_of_fold_of_not_foldDegenerate`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.not_foldDegenerate_of_R_eq_zero {m : Model}
    (hp : Meets m .physical) (hR : m.g.R = 0) : ¬ m.FoldDegenerate := by
  rintro ⟨-, -, hD, -⟩
  rw [Network.Dline, hR] at hD
  simp at hD
  exact hp.2.2.1.ne' hD

end VSMLPF
end powerlib.GFM.Line
