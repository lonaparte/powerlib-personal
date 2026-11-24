import theorem.GridTiedConverter.GFM.Bifurcation
import theorem.NormalForm.BogdanovTakens

/-! # Bogdanov–Takens and fold coefficients of the quasi-static GFM

Kuznetsov's normal-form coefficients of the zero eigenvalue of the quasi-static GFM (the
three-state lossy VSM + power filter and its two-state swing reduction) at a fold, computed from
the field and read through the generic laws of `theorem/NormalForm/BogdanovTakens.lean`.

Model boundary.
* The three-state model `VSMLPFLossy` of `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`,
  unchanged: state `(δ, ω, P_f)`, continuous time, `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P(δ) − P_f)`, `P(δ) = c₀ + A sin(δ − α)` (export-positive active power), read at
  the operating point `(δ*, 0, P_ref)` of a model `VSMLPFLossy.Model`; `K = A cos(δ* − α) =
  P'(δ*)`, `P''(δ*) = −A sin(δ* − α)`; the lossless line is `c₀ = α = 0` (`VSMLPF`).
* Two states (no power filter): the swing model `Synchronous.SwingParams`
  (`theorem/PowerSystem/Synchronous/Swing.lean`) `δ̇ = ω`, `M ω̇ = P_m − P_e(δ) − D ω`,
  `P_e(δ) = k₁ + k₂ sin(δ − k₃)` (the reduced GFM `⟨M, D, P_ref, c₀, A, α⟩`), read at
  `(δ*, 0)`, `K(δ*) = k₂ cos(δ* − k₃)`.
* Excluded: line dynamics (the dynamic-line values are in
  `theorem/GridTiedConverter/GFM/BTCoefficientLine.lean` and `BTCoefficientLineLPF.lean`),
  voltage loop, inner loops, limiting, PLL, delay, PWM.
* Level: the coefficients are Kuznetsov's projection formulas at the operating point, from the
  first and second `fderiv` of the field (`VSMLPFLossy.hasFDerivAt_field`,
  `VSMLPFLossy.fderiv_fderiv_field`, `Synchronous.SwingParams.fderiv_field`,
  `swing_fderiv_fderiv_field`). No normal-form transformation, unfolding or bifurcation
  diagram is asserted and no family is defined: every result is static evidence on the model.

Source: GFM counterpart study, note t3-bifurcation (b) `B3` (the coefficients of the corners
`D = K = 0`: three states `a b < 0`, two states `b = 0`) and (d) `F1`, `F2` (the fold coefficient
`(P_ref − c₀)/(2D)` and the transversality `1/D`), derived symbolically and checked there
(scratch notes outside the repository); Kuznetsov, *Elements of Applied Bifurcation Theory*
(3rd ed., 2004), §5.4 (fold), §8.4 and §8.7 (Bogdanov–Takens).

Results.
* `VSMLPFLossy.fderiv_fderiv_field`: the second derivative `B(u, v) = (0, 0, −ω_c A sin(δ − α)
  u₀ v₀)`, the curvature `P''` of the power characteristic seen by the filter row.
* The corner `D = 0`, `K = 0`, where the zero eigenvalue is double
  (`VSMLPF.two_le_rootMultiplicity_zero_iff`, `theorem/GridTiedConverter/GFM/Bifurcation.lean`):
  the normalised chain `q₀ = (1, 0, 0)`, `q₁ = (0, 1, 0)`, `p₀ = (1, 0, 1/(M ω_c²))`,
  `p₁ = (0, 1, −1/(M ω_c))` (`VSMLPFLossy.Model.isBTChain_of_corner`); for every adjoint chain of
  `(q₀, q₁)`, `a = (P(δ*) − c₀)/(2M) = −P''/(2M)` and `b = −(P(δ*) − c₀)/(M ω_c) = P''/(M ω_c)`
  (`VSMLPFLossy.Model.coeff_of_corner`), i.e. `(P_ref − c₀)/(2M)` and `−(P_ref − c₀)/(M ω_c)` at
  power balance; `a b = −A²/(2 M² ω_c) < 0` for `ω_c > 0`, `A ≠ 0`
  (`VSMLPFLossy.Model.coeffA_mul_coeffB_of_corner`); compare the PI-PLL Liénard form, whose
  quadratic coefficients are `b₂₀ = K_i h''`, `b₁₁ = K_p h''` (`PLL.bt_b20`, `PLL.bt_b11`).
* The damped fold `K = 0`, `D ≠ 0`, where the zero eigenvalue is simple
  (`VSMLPF.rootMultiplicity_zero_le_one`): the normalised null pair `q = (1, 0, 0)`,
  `p = (1, M/D, −1/(D ω_c))` (`VSMLPFLossy.Model.isNullPair_of_fold`); for every normalised
  left null vector, the fold coefficient `a_SN = (P(δ*) − c₀)/(2D)` (`(P_ref − c₀)/(2D)` at
  balance) and the transversality with respect to the set-point `⟨p, ∂f/∂P_ref⟩ = 1/D`
  (`VSMLPFLossy.Model.foldCoeff_of_fold`).
* Two states: `swing_fderiv_fderiv_field` (`B(u, v) = (0, k₂ sin(δ − k₃) u₀ v₀/M)`); the corner
  `D = 0`, `K = 0` is degenerate, `a = (P_e(δ*) − k₁)/(2M)` and `b = 0` for every chain extending
  `(e₁, e₂)`, which is itself a chain (`swing_coeff_of_corner`): the swing friction does not
  depend on the angle; the damped fold has the null pair `(1, 0)`, `(1, M/D)` and
  `a_SN = (P_e(δ*) − k₁)/(2D)`, `⟨p, ∂f/∂P_m⟩ = 1/D` (`swing_foldCoeff_of_fold`).
-/

noncomputable section
namespace powerlib.GFM
open Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)
open powerlib.NormalForm.BogdanovTakens

/-- `⟨(a, b, c), v⟩ = a v₀ + b v₁ + c v₂`. -/
@[tmio T, powerlib_foundation] private theorem inner_mk3 (a b c : ℝ) (v : State 3) :
    ⟪mk3 a b c, v⟫ = a * v 0 + b * v 1 + c * v 2 := by
  simp [mk3, PiLp.inner_apply, Fin.sum_univ_three]; ring

namespace VSMLPFLossy

variable (p : VSMLPFLossy)

@[tmio M, powerlib_domain] private theorem fderiv_eq :
    fderiv ℝ p.field =
      fun y => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (p.toVSMLPF.jacobian (y 0 - p.α)) :=
  funext fun y => (p.hasFDerivAt_field y).fderiv

@[tmio M, powerlib_domain] private theorem jacobian_apply (δ : ℝ) (v : State 3) :
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (p.toVSMLPF.jacobian δ) v =
      mk3 (v 1) (-(p.D * v 1) / p.M - v 2 / p.M)
        (p.ωc * (p.A * Real.cos δ) * v 0 - p.ωc * v 2) := by
  apply state3_ext <;> simp [toEuclideanCLM_apply3, VSMLPF.jacobian, VSMLPFLossy.toVSMLPF] <;>
    ring

/-- The second derivative of the lossy field: `B(u, v) = (0, 0, −ω_c A sin(δ − α) u₀ v₀)`, the
curvature `P''(δ) = −A sin(δ − α)` of the power characteristic seen by the filter row.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_fderiv_field (x u v : State 3) :
    fderiv ℝ (fderiv ℝ p.field) x u v =
      mk3 0 0 (-(p.ωc * (p.A * Real.sin (x 0 - p.α))) * u 0 * v 0) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ p.field) x :=
    ((p.contDiff_field (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x
  rw [fderiv_fderiv_apply hdiff, fderiv_eq]
  simp only [jacobian_apply]
  have hc := ((Real.hasDerivAt_cos (x 0 - p.α)).comp_hasFDerivAt x
    ((Dynamics.hasFDerivAt_coord 0 x).sub_const p.α))
  have hG : HasFDerivAt
      (fun y : State 3 => mk3 (v 1) (-(p.D * v 1) / p.M - v 2 / p.M)
        (p.ωc * (p.A * Real.cos (y 0 - p.α)) * v 0 - p.ωc * v 2))
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
        !![0, 0, 0; 0, 0, 0; -(p.ωc * (p.A * Real.sin (x 0 - p.α))) * v 0, 0, 0]) x := by
    refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
      ![0, 0, (-(p.ωc * (p.A * Real.sin (x 0 - p.α))) * v 0) • Dynamics.coord 0]
      (fun i => ?_) (fun i w => ?_)
    · fin_cases i
      · simpa using (hasFDerivAt_const (v 1) x : HasFDerivAt (fun _ : State 3 => v 1)
          (0 : State 3 →L[ℝ] ℝ) x)
      · simpa using (hasFDerivAt_const (-(p.D * v 1) / p.M - v 2 / p.M) x :
          HasFDerivAt (fun _ : State 3 => -(p.D * v 1) / p.M - v 2 / p.M) (0 : State 3 →L[ℝ] ℝ) x)
      · have h := (((hc.const_mul p.A).const_mul p.ωc).mul_const (v 0)).sub_const (p.ωc * v 2)
        convert h using 1
        · funext y; simp
        · ext w; simp; ring
    · fin_cases i <;> simp [Fin.sum_univ_three]
  rw [hG.fderiv]
  apply state3_ext <;> simp [toEuclideanCLM_apply3]
  ring

/-! ## The Bogdanov–Takens corner `D = 0`, `K = 0` -/

/-- At the corner `D = 0`, `K = A cos(δ* − α) = 0` (`M, ω_c ≠ 0`) the Jacobian at the operating
point has the normalised Bogdanov–Takens chain `q₀ = (1, 0, 0)`, `q₁ = (0, 1, 0)`,
`p₀ = (1, 0, 1/(M ω_c²))`, `p₁ = (0, 1, −1/(M ω_c))`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.isBTChain_of_corner (m : Model) (hM : m.p.M ≠ 0)
    (hω : m.p.ωc ≠ 0) (hD : m.p.D = 0) (hK : m.K = 0) :
    IsBTChain (fderiv ℝ m.p.field m.point) (mk3 1 0 0) (mk3 0 1 0)
      (mk3 1 0 (1 / (m.p.M * m.p.ωc ^ 2))) (mk3 0 1 (-1 / (m.p.M * m.p.ωc))) := by
  have hK' : m.p.A * Real.cos (m.δ - m.p.α) = 0 := hK
  rw [fderiv_eq]
  refine ⟨?_, ?_, fun v => ?_, fun v => ?_, ?_, ?_⟩ <;>
    simp only [Model.point, mk3_zero, jacobian_apply, inner_mk3, mk3_one, mk3_two, hD, hK']
  · apply state3_ext <;> simp
  · apply state3_ext <;> simp
  · field_simp; ring
  · field_simp; ring
  · ring
  · ring

/-- **The Bogdanov–Takens coefficients of the corner.** At `D = 0`, `K = 0` (`M, ω_c ≠ 0`), for
every normalised chain with `q₀ = (1, 0, 0)`, `q₁ = (0, 1, 0)` (one exists,
`Model.isBTChain_of_corner`): `a = (P(δ*) − c₀)/(2M) = −P''(δ*)/(2M)` and
`b = −(P(δ*) − c₀)/(M ω_c) = P''(δ*)/(M ω_c)`, `P''(δ) = −A sin(δ − α)`; at power balance
`P(δ*) = P_ref`, `a = (P_ref − c₀)/(2M)` and `b = −(P_ref − c₀)/(M ω_c)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.coeff_of_corner (m : Model) (hM : m.p.M ≠ 0)
    (hω : m.p.ωc ≠ 0) (hD : m.p.D = 0) (hK : m.K = 0) {p₀ p₁ : State 3}
    (h : IsBTChain (fderiv ℝ m.p.field m.point) (mk3 1 0 0) (mk3 0 1 0) p₀ p₁) :
    coeffA m.p.field m.point (mk3 1 0 0) p₁ = (m.p.Pe m.δ - m.p.c0) / (2 * m.p.M) ∧
      coeffB m.p.field m.point (mk3 1 0 0) (mk3 0 1 0) p₀ p₁ =
        -(m.p.Pe m.δ - m.p.c0) / (m.p.M * m.p.ωc) := by
  have hK' : m.p.A * Real.cos (m.δ - m.p.α) = 0 := hK
  have hP : m.p.Pe m.δ - m.p.c0 = m.p.A * Real.sin (m.δ - m.p.α) := by simp [Pe]
  rw [hP]
  set β := -(m.p.ωc * (m.p.A * Real.sin (m.δ - m.p.α)))
  have hJ : ∀ v : State 3, fderiv ℝ m.p.field m.point v =
      mk3 (v 1) (-v 2 / m.p.M) (-(m.p.ωc * v 2)) := fun v => by
    rw [fderiv_eq]
    simp only [Model.point, mk3_zero, jacobian_apply, hD, hK']
    apply state3_ext <;> simp [neg_div]
  have hB : ∀ u v : State 3,
      fderiv ℝ (fderiv ℝ m.p.field) m.point u v = mk3 0 0 (β * u 0 * v 0) :=
    fun u v => by rw [fderiv_fderiv_field]; simp [Model.point, β]
  have hy : fderiv ℝ (fderiv ℝ m.p.field) m.point (mk3 1 0 0) (mk3 1 0 0) =
      fderiv ℝ m.p.field m.point (mk3 0 0 (-β / m.p.ωc)) +
        (-β / (m.p.M * m.p.ωc)) • mk3 0 1 0 := by
    rw [hB, hJ]
    apply state3_ext <;> simp <;> field_simp
    ring
  have hz : mk3 0 0 (-β / m.p.ωc) +
      fderiv ℝ (fderiv ℝ m.p.field) m.point (mk3 1 0 0) (mk3 0 1 0) =
      fderiv ℝ m.p.field m.point (mk3 0 0 (β / m.p.ωc ^ 2)) +
        (β / (m.p.M * m.p.ωc ^ 2)) • mk3 0 1 0 := by
    rw [hB, hJ]
    apply state3_ext <;> simp <;> field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [h.coeffA_eq hy]; simp only [β]; field_simp
  · rw [h.coeffB_eq hy hz]; simp only [β]; field_simp

/-- **`ab < 0` at the corner.** With `A ≠ 0`, `M ≠ 0` and `ω_c > 0`, the product of the
Bogdanov–Takens coefficients is `a b = −A²/(2 M² ω_c) < 0` (at the corner `sin²(δ* − α) = 1`);
compare the quadratic coefficients `b₂₀ = K_i h''`, `b₁₁ = K_p h''` of the PI-PLL Liénard form
(`theorem/GridTiedConverter/PLL/PIPLLLienard.lean`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.coeffA_mul_coeffB_of_corner (m : Model)
    (hM : m.p.M ≠ 0) (hω : 0 < m.p.ωc) (hA : m.p.A ≠ 0) (hD : m.p.D = 0) (hK : m.K = 0)
    {p₀ p₁ : State 3}
    (h : IsBTChain (fderiv ℝ m.p.field m.point) (mk3 1 0 0) (mk3 0 1 0) p₀ p₁) :
    coeffA m.p.field m.point (mk3 1 0 0) p₁ *
        coeffB m.p.field m.point (mk3 1 0 0) (mk3 0 1 0) p₀ p₁ =
      -(m.p.A ^ 2) / (2 * m.p.M ^ 2 * m.p.ωc) ∧
    coeffA m.p.field m.point (mk3 1 0 0) p₁ *
        coeffB m.p.field m.point (mk3 1 0 0) (mk3 0 1 0) p₀ p₁ < 0 := by
  have hcos : Real.cos (m.δ - m.p.α) = 0 :=
    (mul_eq_zero.mp (show m.p.A * Real.cos (m.δ - m.p.α) = 0 from hK)).resolve_left hA
  have hs : Real.sin (m.δ - m.p.α) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (m.δ - m.p.α)]
  obtain ⟨ha, hb⟩ := m.coeff_of_corner hM hω.ne' hD hK h
  have he : coeffA m.p.field m.point (mk3 1 0 0) p₁ *
      coeffB m.p.field m.point (mk3 1 0 0) (mk3 0 1 0) p₀ p₁ =
      -(m.p.A ^ 2) / (2 * m.p.M ^ 2 * m.p.ωc) := by
    rw [ha, hb]
    simp only [Pe, add_sub_cancel_left]
    rw [show m.p.A * Real.sin (m.δ - m.p.α) / (2 * m.p.M) *
        (-(m.p.A * Real.sin (m.δ - m.p.α)) / (m.p.M * m.p.ωc)) =
        -(m.p.A ^ 2 * Real.sin (m.δ - m.p.α) ^ 2) / (2 * m.p.M ^ 2 * m.p.ωc) by
      field_simp, hs, mul_one]
  refine ⟨he, ?_⟩
  rw [he]
  have : 0 < m.p.A ^ 2 := by positivity
  have : 0 < 2 * m.p.M ^ 2 * m.p.ωc := by positivity
  rw [neg_div]
  exact neg_neg_of_pos (by positivity)

/-! ## The damped fold `K = 0`, `D ≠ 0` -/

/-- At a fold `K = 0` with damping (`M, D, ω_c ≠ 0`) the zero eigenvalue of the Jacobian at the
operating point has the normalised null pair `q = (1, 0, 0)`, `p = (1, M/D, −1/(D ω_c))`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.isNullPair_of_fold (m : Model) (hM : m.p.M ≠ 0)
    (hD : m.p.D ≠ 0) (hω : m.p.ωc ≠ 0) (hK : m.K = 0) :
    IsNullPair (fderiv ℝ m.p.field m.point) (mk3 1 0 0)
      (mk3 1 (m.p.M / m.p.D) (-1 / (m.p.D * m.p.ωc))) := by
  have hK' : m.p.A * Real.cos (m.δ - m.p.α) = 0 := hK
  rw [fderiv_eq]
  refine ⟨?_, fun v => ?_, ?_⟩ <;>
    simp only [Model.point, mk3_zero, jacobian_apply, inner_mk3, mk3_one, mk3_two, hK']
  · apply state3_ext <;> simp
  · field_simp; ring
  · ring

/-- **The fold (saddle-node) coefficient and its transversality.** At a fold `K = 0` with
damping (`M, D, ω_c ≠ 0`), for every normalised left null vector `p` of `q = (1, 0, 0)` (one
exists, `Model.isNullPair_of_fold`): `a_SN = ½ ⟨p, B(q, q)⟩ = (P(δ*) − c₀)/(2D)`
(`= (P_ref − c₀)/(2D)` at balance), and the transversality with respect to the set-point is
`⟨p, ∂f/∂P_ref⟩ = 1/D`. Both are Kuznetsov's coefficients; the centre-manifold reduction they
summarise is not formalized.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_of_fold (m : Model) (hM : m.p.M ≠ 0)
    (hD : m.p.D ≠ 0) (hω : m.p.ωc ≠ 0) (hK : m.K = 0) {q : State 3}
    (h : IsNullPair (fderiv ℝ m.p.field m.point) (mk3 1 0 0) q) :
    foldCoeff m.p.field m.point (mk3 1 0 0) q = (m.p.Pe m.δ - m.p.c0) / (2 * m.p.D) ∧
      foldTransversality (fun μ => ({ m.p with Pref := μ } : VSMLPFLossy).field) m.p.Pref
        m.point q = 1 / m.p.D := by
  have hK' : m.p.A * Real.cos (m.δ - m.p.α) = 0 := hK
  have hP : m.p.Pe m.δ - m.p.c0 = m.p.A * Real.sin (m.δ - m.p.α) := by simp [Pe]
  rw [hP]
  set β := -(m.p.ωc * (m.p.A * Real.sin (m.δ - m.p.α)))
  have hJ : ∀ v : State 3, fderiv ℝ m.p.field m.point v =
      mk3 (v 1) (-(m.p.D * v 1) / m.p.M - v 2 / m.p.M) (-(m.p.ωc * v 2)) := fun v => by
    rw [fderiv_eq]
    simp only [Model.point, mk3_zero, jacobian_apply, hK']
    apply state3_ext <;> simp
  have hy : fderiv ℝ (fderiv ℝ m.p.field) m.point (mk3 1 0 0) (mk3 1 0 0) =
      fderiv ℝ m.p.field m.point (mk3 0 (β / (m.p.D * m.p.ωc)) (-β / m.p.ωc)) +
        (-β / (m.p.D * m.p.ωc)) • mk3 1 0 0 := by
    rw [fderiv_fderiv_field, hJ]
    apply state3_ext <;> simp only [Model.point, mk3_zero, mk3_one, mk3_two, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, β] <;> field_simp <;> ring
  have hF : (fun μ => ({ m.p with Pref := μ } : VSMLPFLossy).field m.point) =
      fun μ => m.p.field m.point + (μ - m.p.Pref) • mk3 0 (1 / m.p.M) 0 := by
    funext μ
    apply state3_ext <;> simp only [VSMLPFLossy.field, Pe, mk3_zero, mk3_one, mk3_two,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring
  have hd : deriv (fun μ => ({ m.p with Pref := μ } : VSMLPFLossy).field m.point) m.p.Pref =
      mk3 0 (1 / m.p.M) 0 := by
    rw [hF]
    have := (((hasDerivAt_id m.p.Pref).sub_const m.p.Pref).smul_const
      (mk3 0 (1 / m.p.M) 0)).const_add (m.p.field m.point)
    simpa using this.deriv
  have ht : deriv (fun μ => ({ m.p with Pref := μ } : VSMLPFLossy).field m.point) m.p.Pref =
      fderiv ℝ m.p.field m.point (mk3 0 (-1 / m.p.D) 0) + (1 / m.p.D) • mk3 1 0 0 := by
    rw [hd, hJ]
    apply state3_ext <;> simp only [mk3_zero, mk3_one, mk3_two, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] <;> field_simp <;> ring
  refine ⟨?_, ?_⟩
  · rw [h.foldCoeff_eq hy]; simp only [β]; field_simp
  · exact IsNullPair.foldTransversality_eq (F := fun μ => ({ m.p with Pref := μ } :
      VSMLPFLossy).field) h ht

end VSMLPFLossy
/-! ## Two states: the swing model -/

/-- `⟨(a, b), v⟩ = a v₀ + b v₁`. -/
@[tmio T, powerlib_foundation] private theorem inner_mk (a b : ℝ) (v : State 2) :
    ⟪PhasePlane.mk a b, v⟫ = a * v 0 + b * v 1 := by
  simp [PhasePlane.mk, PiLp.inner_apply, Fin.sum_univ_two]; ring

@[tmio M, powerlib_domain] private theorem swing_jacobian_apply (p : Synchronous.SwingParams)
    (δ : ℝ) (v : State 2) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.jacobian δ) v =
      PhasePlane.mk (v 1) (-(p.k₂ * Real.cos (δ - p.k₃)) / p.M * v 0 - p.D / p.M * v 1) := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;>
    simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two, Synchronous.SwingParams.jacobian,
      Synchronous.SwingParams.syncCoeff]
  ring

/-- The second derivative of the swing field: `B(u, v) = (0, k₂ sin(δ − k₃) u₀ v₀/M)`, i.e.
`−P_e''(δ) u₀ v₀/M`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem swing_fderiv_fderiv_field (p : Synchronous.SwingParams)
    (x u v : State 2) :
    fderiv ℝ (fderiv ℝ p.field) x u v =
      PhasePlane.mk 0 (p.k₂ * Real.sin (x 0 - p.k₃) * u 0 * v 0 / p.M) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ p.field) x :=
    ((p.contDiff_field (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x
  rw [fderiv_fderiv_apply hdiff, show fderiv ℝ p.field = fun y => Matrix.toEuclideanCLM
    (n := Fin 2) (𝕜 := ℝ) (p.jacobian (y 0)) from funext p.fderiv_field]
  simp only [swing_jacobian_apply]
  have hc := ((Real.hasDerivAt_cos (x 0 - p.k₃)).comp_hasFDerivAt x
    ((Dynamics.hasFDerivAt_coord 0 x).sub_const p.k₃))
  have hG : HasFDerivAt
      (fun y : State 2 => PhasePlane.mk (v 1)
        (-(p.k₂ * Real.cos (y 0 - p.k₃)) / p.M * v 0 - p.D / p.M * v 1))
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        !![0, 0; p.k₂ * Real.sin (x 0 - p.k₃) * v 0 / p.M, 0]) x := by
    refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
      ![0, (p.k₂ * Real.sin (x 0 - p.k₃) * v 0 / p.M) • Dynamics.coord 0]
      (fun i => ?_) (fun i w => ?_)
    · fin_cases i
      · simpa using (hasFDerivAt_const (v 1) x : HasFDerivAt (fun _ : State 2 => v 1)
          (0 : State 2 →L[ℝ] ℝ) x)
      · have h := ((((hc.const_mul p.k₂).neg.mul_const p.M⁻¹).mul_const (v 0)).sub_const
          (p.D / p.M * v 1))
        convert h using 1
        · funext y; simp; ring
        · ext w; simp; ring
    · fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hG.fderiv]
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;>
    simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]
  ring

/-- **The two-state corner is degenerate.** At `D = 0`, `K(δ*) = k₂ cos(δ* − k₃) = 0`
(`M ≠ 0`) the swing Jacobian is the Jordan block with the chain `(e₁, e₂, e₁, e₂)`, and for
every normalised chain with `q₀ = e₁`, `q₁ = e₂`: `a = (P_e(δ*) − k₁)/(2M) = −P_e''(δ*)/(2M)`
and `b = 0` (the swing friction does not depend on the angle). Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem swing_coeff_of_corner (p : Synchronous.SwingParams)
    (hM : p.M ≠ 0) (hD : p.D = 0) {δ : ℝ} (hK : p.syncCoeff δ = 0) :
    IsBTChain (fderiv ℝ p.field (PhasePlane.mk δ 0)) (PhasePlane.mk 1 0) (PhasePlane.mk 0 1)
        (PhasePlane.mk 1 0) (PhasePlane.mk 0 1) ∧
      ∀ {p₀ p₁ : State 2}, IsBTChain (fderiv ℝ p.field (PhasePlane.mk δ 0))
          (PhasePlane.mk 1 0) (PhasePlane.mk 0 1) p₀ p₁ →
        coeffA p.field (PhasePlane.mk δ 0) (PhasePlane.mk 1 0) p₁ =
            (p.Pe δ - p.k₁) / (2 * p.M) ∧
          coeffB p.field (PhasePlane.mk δ 0) (PhasePlane.mk 1 0) (PhasePlane.mk 0 1) p₀ p₁ = 0 := by
  have hK' : p.k₂ * Real.cos (δ - p.k₃) = 0 := hK
  have hJ : ∀ v : State 2, fderiv ℝ p.field (PhasePlane.mk δ 0) v = PhasePlane.mk (v 1) 0 :=
    fun v => by
      rw [p.fderiv_field, PhasePlane.mk_apply_zero, swing_jacobian_apply, hK', hD]
      simp
  have hB : ∀ u v : State 2, fderiv ℝ (fderiv ℝ p.field) (PhasePlane.mk δ 0) u v =
      PhasePlane.mk 0 (p.k₂ * Real.sin (δ - p.k₃) * u 0 * v 0 / p.M) := fun u v => by
    rw [swing_fderiv_fderiv_field, PhasePlane.mk_apply_zero]
  refine ⟨⟨?_, ?_, fun v => ?_, fun v => ?_, ?_, ?_⟩, fun {p₀ p₁} h => ?_⟩
  · rw [hJ]; simp
  · rw [hJ]; simp
  · rw [hJ, inner_mk]; simp
  · rw [hJ, inner_mk, inner_mk]; simp
  · rw [inner_mk]; simp
  · rw [inner_mk]; simp
  have hy : fderiv ℝ (fderiv ℝ p.field) (PhasePlane.mk δ 0) (PhasePlane.mk 1 0)
      (PhasePlane.mk 1 0) = fderiv ℝ p.field (PhasePlane.mk δ 0) 0 +
        (p.k₂ * Real.sin (δ - p.k₃) / p.M) • PhasePlane.mk 0 1 := by
    rw [hB, hJ]
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;> simp
  have hz : (0 : State 2) + fderiv ℝ (fderiv ℝ p.field) (PhasePlane.mk δ 0) (PhasePlane.mk 1 0)
      (PhasePlane.mk 0 1) = fderiv ℝ p.field (PhasePlane.mk δ 0) 0 +
        (0 : ℝ) • PhasePlane.mk 0 1 := by
    rw [hB, hJ]
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;> simp
  refine ⟨?_, h.coeffB_eq hy hz⟩
  rw [h.coeffA_eq hy]
  simp only [Synchronous.SwingParams.Pe, add_sub_cancel_left]
  field_simp

/-- **The two-state fold.** At a fold `K(δ*) = 0` with damping (`M, D ≠ 0`) the null pair is
`q = (1, 0)`, `p = (1, M/D)`, and for every normalised left null vector of `q`: the fold
coefficient `a_SN = (P_e(δ*) − k₁)/(2D)` and the transversality with respect to the mechanical
(set-point) power `⟨p, ∂f/∂P_m⟩ = 1/D`, the values of the three-state model
(`VSMLPFLossy.Model.foldCoeff_of_fold`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem swing_foldCoeff_of_fold (p : Synchronous.SwingParams)
    (hM : p.M ≠ 0) (hD : p.D ≠ 0) {δ : ℝ} (hK : p.syncCoeff δ = 0) :
    IsNullPair (fderiv ℝ p.field (PhasePlane.mk δ 0)) (PhasePlane.mk 1 0)
        (PhasePlane.mk 1 (p.M / p.D)) ∧
      ∀ {q : State 2}, IsNullPair (fderiv ℝ p.field (PhasePlane.mk δ 0)) (PhasePlane.mk 1 0) q →
        foldCoeff p.field (PhasePlane.mk δ 0) (PhasePlane.mk 1 0) q = (p.Pe δ - p.k₁) / (2 * p.D) ∧
          foldTransversality (fun μ => ({ p with Pm := μ } : Synchronous.SwingParams).field)
            p.Pm (PhasePlane.mk δ 0) q = 1 / p.D := by
  have hK' : p.k₂ * Real.cos (δ - p.k₃) = 0 := hK
  have hJ : ∀ v : State 2, fderiv ℝ p.field (PhasePlane.mk δ 0) v =
      PhasePlane.mk (v 1) (-(p.D / p.M * v 1)) := fun v => by
    rw [p.fderiv_field, PhasePlane.mk_apply_zero, swing_jacobian_apply, hK']
    simp
  refine ⟨⟨?_, fun v => ?_, ?_⟩, fun {q} h => ⟨?_, ?_⟩⟩
  · rw [hJ]; simp
  · rw [hJ, inner_mk]; simp; field_simp; ring
  · rw [inner_mk]; simp
  · have hy : fderiv ℝ (fderiv ℝ p.field) (PhasePlane.mk δ 0) (PhasePlane.mk 1 0)
        (PhasePlane.mk 1 0) = fderiv ℝ p.field (PhasePlane.mk δ 0)
          (PhasePlane.mk 0 (-(p.k₂ * Real.sin (δ - p.k₃)) / p.D)) +
          (p.k₂ * Real.sin (δ - p.k₃) / p.D) • PhasePlane.mk 1 0 := by
      rw [swing_fderiv_fderiv_field, hJ]
      refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;> simp <;> field_simp
      ring
    rw [h.foldCoeff_eq hy]
    simp only [Synchronous.SwingParams.Pe, add_sub_cancel_left]
    field_simp
  · have hF : (fun μ => ({ p with Pm := μ } : Synchronous.SwingParams).field
        (PhasePlane.mk δ 0)) = fun μ => p.field (PhasePlane.mk δ 0) +
          (μ - p.Pm) • PhasePlane.mk 0 (1 / p.M) := by
      funext μ
      refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;>
        simp [Synchronous.SwingParams.field, Synchronous.SwingParams.accel,
          Synchronous.SwingParams.Pe]
      ring
    have hd : deriv (fun μ => ({ p with Pm := μ } : Synchronous.SwingParams).field
        (PhasePlane.mk δ 0)) p.Pm = PhasePlane.mk 0 (1 / p.M) := by
      rw [hF]
      have := (((hasDerivAt_id p.Pm).sub_const p.Pm).smul_const
        (PhasePlane.mk 0 (1 / p.M))).const_add (p.field (PhasePlane.mk δ 0))
      simpa using this.deriv
    have ht : deriv (fun μ => ({ p with Pm := μ } : Synchronous.SwingParams).field
        (PhasePlane.mk δ 0)) p.Pm = fderiv ℝ p.field (PhasePlane.mk δ 0)
          (PhasePlane.mk 0 (-1 / p.D)) + (1 / p.D) • PhasePlane.mk 1 0 := by
      rw [hd, hJ]
      refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
      · simp; field_simp; ring
      · simp; field_simp
    exact IsNullPair.foldTransversality_eq (F := fun μ =>
      ({ p with Pm := μ } : Synchronous.SwingParams).field) h ht

end powerlib.GFM
