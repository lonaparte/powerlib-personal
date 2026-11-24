import theorem.GridTiedConverter.GFM.BifurcationLine
import theorem.NormalForm.BogdanovTakens

/-! # The Bogdanov–Takens coefficients of the VSM on a dynamic R–L line

Kuznetsov's normal-form coefficients `a`, `b` of the double zero eigenvalue of the four-state VSM
on a dynamic line at its Bogdanov–Takens point (a fold `K = 0` with the damping `D = D_line`),
in closed form, read through the generic laws of `theorem/NormalForm/BogdanovTakens.lean`.

Model boundary.
The four-state model `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
state `(δ, ω, i_d, i_q)`, grid dq frame at `ω₀`, `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`,
`L i̇ = E e^{jδ} − V − (R + jX) i`, export-positive active power, constant `E`; no voltage loop,
inner loops, LC filter, limiting, PLL, delay or PWM. A model `Line.VSM.Model` is read at its
operating point `(δ*, 0, i_s(δ*))`; `P(δ*)` is the quasi-steady power there (`P_ref` at
balance), `c₀ = E² R/|Z|²`, `K = A cos(δ* − α)`, `D_line = 2 E² R X L/|Z|⁴`; the Jordan chain is
`q₀ = (1, 0, i_s'(δ*))`, `q₁ = (0, 1, w)` of `Line.VSM.Model.jordan_chain_of_bt`
(`theorem/GridTiedConverter/GFM/BifurcationLine.lean`). Level: the coefficients are Kuznetsov's
projection formulas from the first and second `fderiv` of the field at the operating point; no
normal-form transformation, unfolding, Hopf or homoclinic curve or criticality is asserted and
no family is defined: every result is static evidence on the model.

Source: GFM counterpart study, note t3-bifurcation (b) (the BT point of the dynamic line at
`D_BT = D_line`, its coefficients and the sign of `a b` computed numerically on 20 random sets,
script s2b); the closed forms below were derived for this module and checked with exact rational
arithmetic on 24 parameter sets (scratch notes outside the repository); Kuznetsov, *Elements of
Applied Bifurcation Theory* (3rd ed., 2004), §8.4 and §8.7.

Results.
* `Line.VSM.fderiv_fderiv_field`: the second derivative of the field at every state,
  `B(u, v) = (0, (P_e u₀v₀ + E sin δ (u₀v₂ + u₂v₀) − E cos δ (u₀v₃ + u₃v₀))/M,
  −E cos δ u₀v₀/L, −E sin δ u₀v₀/L)`.
* `Line.VSM.Model.fold_coords`: at a fold `X cos δ* + R sin δ* = 0`, i.e. `cos δ* = −R k/|Z|²`,
  `sin δ* = X k/|Z|²` with `k² = |Z|²`.
* The effective inertia `n = M + E² L² X (3R² − X²)/|Z|⁶` (`Line.VSM.btInertia`), the
  normalisation of the left null vector.
* `Line.VSM.Model.coeff_of_bt`: at a fold (`n ≠ 0`), for every normalised chain extending
  `(q₀, q₁)`, `a = (P(δ*) − c₀)/(2n)` and `b = 2 (P(δ*) − c₀) L² (R² − X²) D_line/(|Z|⁴ n²)`
  (through the decompositions `B(q₀, q₀) = J y + 2a q₁`, `y + B(q₀, q₁) = J z + b q₁` of
  `NormalForm.BogdanovTakens.IsBTChain.coeffA_eq`, `IsBTChain.coeffB_eq`). The quasi-static
  value `a = (P − c₀)/(2M)` of the three-state corner
  (`theorem/GridTiedConverter/GFM/BTCoefficient.lean`) has `M` in place of `n`.
* `Line.VSM.Model.exists_isBTChain_of_bt`: at `D = D_line` the chain exists, with
  `p₁ = (D_line, M, L E (X sin δ* − R cos δ*)/|Z|², 0)/n` (`IsBTChain.exists_of_left`).
* `Line.VSM.Model.coeffA_mul_coeffB_pos_iff`: for `R, X, L > 0`, `E V ≠ 0`, `n > 0`,
  `a b = (P(δ*) − c₀)² L² (R² − X²) D_line/(|Z|⁴ n³)`, so `a b > 0` iff `X < R` and `a b < 0`
  iff `R < X`.
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)
open powerlib.NormalForm.BogdanovTakens

namespace VSM

variable (g : VSM)

/-- The second derivative of the four-state field at a state `x`:
`B(u, v) = (0, (P_e u₀v₀ + E sin δ (u₀v₂ + u₂v₀) − E cos δ (u₀v₃ + u₃v₀))/M,
−E cos δ u₀v₀/L, −E sin δ u₀v₀/L)`, `δ = x₀`, `P_e = P_e(x)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_fderiv_field (x u v : State 4) :
    fderiv ℝ (fderiv ℝ g.field) x u v = WithLp.toLp 2 ![0,
      (g.power (x 0) (x 2) (x 3) * u 0 * v 0 + g.E * Real.sin (x 0) * (u 0 * v 2 + u 2 * v 0) -
        g.E * Real.cos (x 0) * (u 0 * v 3 + u 3 * v 0)) / g.M,
      -(g.E * Real.cos (x 0)) * u 0 * v 0 / g.L, -(g.E * Real.sin (x 0)) * u 0 * v 0 / g.L] := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ g.field) x :=
    ((g.contDiff_field (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x
  rw [fderiv_fderiv_apply hdiff, show fderiv ℝ g.field = fun y => Matrix.toEuclideanCLM
    (n := Fin 4) (𝕜 := ℝ) (g.jacobian (y 0) (y 2) (y 3)) from funext g.fderiv_field]
  set P := g.power (x 0) (x 2) (x 3)
  set c := Real.cos (x 0)
  set s := Real.sin (x 0)
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x (hasFDerivAt_coord 0 x)
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x (hasFDerivAt_coord 0 x)
  have hG : HasFDerivAt
      (fun y : State 4 => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (g.jacobian (y 0) (y 2) (y 3)) v)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        !![0, 0, 0, 0;
          (P * v 0 + g.E * s * v 2 - g.E * c * v 3) / g.M, 0, g.E * s * v 0 / g.M,
            -(g.E * c * v 0) / g.M;
          -(g.E * c * v 0) / g.L, 0, 0, 0;
          -(g.E * s * v 0) / g.L, 0, 0, 0]) x := by
    refine hasFDerivAt_toEuclideanCLM_of_components _
      ![0, ((P * v 0 + g.E * s * v 2 - g.E * c * v 3) / g.M) • coord 0 +
          (g.E * s * v 0 / g.M) • coord 2 + (-(g.E * c * v 0) / g.M) • coord 3,
        (-(g.E * c * v 0) / g.L) • coord 0, (-(g.E * s * v 0) / g.L) • coord 0]
      (fun i => ?_) (fun i w => ?_)
    · fin_cases i
      · show HasFDerivAt (fun y : State 4 => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 2) (y 3)) v 0) 0 x
        have : (fun y : State 4 => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 2) (y 3)) v 0) = fun _ => v 1 := by
          funext y; simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_four]
        rw [this]; exact hasFDerivAt_const _ _
      · show HasFDerivAt (fun y : State 4 => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 2) (y 3)) v 1) _ x
        have h2 := hasFDerivAt_coord 2 x
        have h3 := hasFDerivAt_coord 3 x
        have h := ((((((hs.mul h2).sub (hc.mul h3)).const_mul g.E).mul_const (v 0)).sub_const
          (g.D * v 1)).sub ((hc.const_mul g.E).mul_const (v 2))).sub
          ((hs.const_mul g.E).mul_const (v 3))
        have h' := h.mul_const g.M⁻¹
        convert h' using 1
        · funext y
          simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_four,
            Network.reactive_eq]
          ring
        · ext w
          simp [P, Network.power_eq]
          ring
      · show HasFDerivAt (fun y : State 4 => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 2) (y 3)) v 2) _ x
        have h := ((((hs.const_mul g.E).neg.mul_const (v 0)).sub_const (g.R * v 2)).add_const
          (g.X * v 3)).mul_const g.L⁻¹
        convert h using 1
        · funext y
          simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_four]
          ring
        · ext w
          simp
          ring
      · show HasFDerivAt (fun y : State 4 => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 2) (y 3)) v 3) _ x
        have h := ((((hc.const_mul g.E).mul_const (v 0)).sub_const (g.X * v 2)).sub_const
          (g.R * v 3)).mul_const g.L⁻¹
        convert h using 1
        · funext y
          simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_four]
          ring
        · ext w
          simp
          ring
    · fin_cases i <;> simp [Fin.sum_univ_four]
  rw [hG.fderiv]
  ext i
  fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four] <;> ring

/-- The effective inertia of the Bogdanov–Takens point of the dynamic line,
`n = M + E² L² X (3R² − X²)/|Z|⁶`: the normalisation `⟨p̃₁, q₁⟩` of the left null vector
`p̃₁ = (D_line, M, L E (X sin δ − R cos δ)/|Z|², 0)` at a fold. -/
def btInertia : ℝ := g.M + g.E ^ 2 * g.L ^ 2 * g.X * (3 * g.R ^ 2 - g.X ^ 2) / g.absSq ^ 3

/-- At a fold `K = 0` (`E V ≠ 0`, `|Z|² > 0`): `X cos δ* + R sin δ* = 0`. -/
@[tmio M, powerlib_domain] private theorem fold_relation (m : Model) (hZ : 0 < m.g.absSq)
    (hV : m.g.E * m.g.V ≠ 0) (hK : m.K = 0) :
    m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ = 0 := by
  have hs := Real.sqrt_pos.mpr hZ
  have hss := Real.sq_sqrt hZ.le
  have h : m.K = m.g.E * m.g.V * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq := by
    rw [Model.K, Network.syncCoeff, Real.cos_sub, m.g.sin_α, m.g.cos_α hZ, Network.A]
    set sq := Real.sqrt m.g.absSq
    rw [← hss]
    field_simp
  rw [h, div_eq_zero_iff, mul_eq_zero] at hK
  rcases hK with (hK | hK) | hK
  · exact absurd hK hV
  · exact hK
  · exact absurd hK hZ.ne'

/-- **Fold coordinates.** At a fold `K = 0` (`E V ≠ 0`, `|Z|² > 0`), `cos δ* = −R k/|Z|²`,
`sin δ* = X k/|Z|²` and `k² = |Z|²` for `k = X sin δ* − R cos δ*`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.fold_coords (m : Model) (hZ : 0 < m.g.absSq)
    (hV : m.g.E * m.g.V ≠ 0) (hK : m.K = 0) :
    ∃ k : ℝ, Real.cos m.δ = -(m.g.R * k) / (m.g.R ^ 2 + m.g.X ^ 2) ∧
      Real.sin m.δ = m.g.X * k / (m.g.R ^ 2 + m.g.X ^ 2) ∧ k ^ 2 = m.g.R ^ 2 + m.g.X ^ 2 := by
  have hu := fold_relation m hZ hV hK
  have hZ' : m.g.R ^ 2 + m.g.X ^ 2 ≠ 0 := hZ.ne'
  refine ⟨m.g.X * Real.sin m.δ - m.g.R * Real.cos m.δ, ?_, ?_, ?_⟩
  · field_simp
    linear_combination m.g.X * hu
  · field_simp
    linear_combination m.g.R * hu
  · linear_combination (m.g.R ^ 2 + m.g.X ^ 2) * Real.sin_sq_add_cos_sq m.δ -
      (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) * hu

/-- **The Bogdanov–Takens coefficients of the dynamic line.** At a fold `K = 0` (`M, L ≠ 0`,
`|Z|² > 0`, `E V ≠ 0`) with `n = btInertia ≠ 0`, for every normalised chain with the Jordan chain
`q₀ = (1, 0, i_s'(δ*))`, `q₁ = (0, 1, w)` of `Model.jordan_chain_of_bt` (one exists at
`D = D_line`, `Model.exists_isBTChain_of_bt`):
`a = (P(δ*) − c₀)/(2n)` and `b = 2 (P(δ*) − c₀) L² (R² − X²) D_line/(|Z|⁴ n²)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.coeff_of_bt (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hV : m.g.E * m.g.V ≠ 0) (hK : m.K = 0)
    (hn : m.g.btInertia ≠ 0) {p₀ p₁ : State 4}
    (h : IsBTChain (fderiv ℝ m.g.field m.point) (WithLp.toLp 2 m.tangent)
      (WithLp.toLp 2 m.chain) p₀ p₁) :
    coeffA m.g.field m.point (WithLp.toLp 2 m.tangent) p₁ =
        (m.g.qssPower m.δ - m.g.c0) / (2 * m.g.btInertia) ∧
      coeffB m.g.field m.point (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.chain) p₀ p₁ =
        2 * (m.g.qssPower m.δ - m.g.c0) * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) * m.g.Dline /
          (m.g.absSq ^ 2 * m.g.btInertia ^ 2) := by
  obtain ⟨k, hc, hs, hk⟩ := m.fold_coords hZ hV hK
  have hZ' : m.g.R ^ 2 + m.g.X ^ 2 ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = m.g.btInertia := ⟨_, rfl⟩
  rw [← hn_def] at hn ⊢
  have hnv : n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 = m.g.M * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 +
      m.g.E ^ 2 * m.g.L ^ 2 * m.g.X * (3 * m.g.R ^ 2 - m.g.X ^ 2) := by
    rw [hn_def, btInertia, habs]
    field_simp
  set P := m.g.qssPower m.δ with hP
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = (P - m.g.c0) / n := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 2 * (P - m.g.c0) * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) *
      m.g.Dline / (m.g.absSq ^ 2 * n ^ 2) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y : ℝ, y = -(m.g.L * (m.g.R * (-(m.g.E * Real.cos m.δ) / m.g.L -
      c1 * m.chain 2) + m.g.X * (-(m.g.E * Real.sin m.δ) / m.g.L - c1 * m.chain 3))) /
      m.g.absSq := ⟨_, rfl⟩
  obtain ⟨y3, hy3⟩ : ∃ y : ℝ, y = m.g.L * (m.g.X * (-(m.g.E * Real.cos m.δ) / m.g.L -
      c1 * m.chain 2) - m.g.R * (-(m.g.E * Real.sin m.δ) / m.g.L - c1 * m.chain 3)) /
      m.g.absSq := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z : ℝ, z = -(m.g.L * (m.g.R * (y2 - d * m.chain 2) +
      m.g.X * (y3 - d * m.chain 3))) / m.g.absSq := ⟨_, rfl⟩
  obtain ⟨z3, hz3⟩ : ∃ z : ℝ, z = m.g.L * (m.g.X * (y2 - d * m.chain 2) -
      m.g.R * (y3 - d * m.chain 3)) / m.g.absSq := ⟨_, rfl⟩
  have hpt : ∀ i, m.point i = ![m.δ, 0, (m.g.is m.δ).re, (m.g.is m.δ).im] i := fun i => by
    fin_cases i <;> rfl
  have hB : ∀ u v : State 4, fderiv ℝ (fderiv ℝ m.g.field) m.point u v = WithLp.toLp 2 ![0,
      (P * u 0 * v 0 + m.g.E * Real.sin m.δ * (u 0 * v 2 + u 2 * v 0) -
        m.g.E * Real.cos m.δ * (u 0 * v 3 + u 3 * v 0)) / m.g.M,
      -(m.g.E * Real.cos m.δ) * u 0 * v 0 / m.g.L,
      -(m.g.E * Real.sin m.δ) * u 0 * v 0 / m.g.L] := fun u v => by
    rw [fderiv_fderiv_field, hpt 0, hpt 2, hpt 3]; rfl
  have hJ : ∀ v : Fin 4 → ℝ, fderiv ℝ m.g.field m.point (WithLp.toLp 2 v) =
      WithLp.toLp 2 (m.jac *ᵥ v) := fun v => by
    rw [m.fderiv_point, Matrix.toEuclideanCLM_toLp]
  have hy : fderiv ℝ (fderiv ℝ m.g.field) m.point (WithLp.toLp 2 m.tangent)
      (WithLp.toLp 2 m.tangent) =
      fderiv ℝ m.g.field m.point (WithLp.toLp 2 ![0, 0, y2, y3]) +
        c1 • WithLp.toLp 2 m.chain := by
    rw [hB, hJ]
    ext i
    fin_cases i <;>
      simp [Model.jac, VSM.jacobian, Model.tangent, Model.chain, hy2, hy3, hc1, hc, hs, habs,
        Network.c0]
    · linear_combination (norm := skip) (-(m.g.E ^ 2 * (m.g.L ^ 2 * m.g.X *
        (3 * m.g.R ^ 2 - m.g.X ^ 2) * (P * (m.g.R ^ 2 + m.g.X ^ 2) - m.g.E ^ 2 * m.g.R) +
        n * m.g.R * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3)) / (m.g.M * n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 5)) *
        hk + ((P * (m.g.R ^ 2 + m.g.X ^ 2) - m.g.E ^ 2 * m.g.R) /
          (m.g.M * n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 4)) * hnv
      field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
  have hz : WithLp.toLp 2 ![0, 0, y2, y3] + fderiv ℝ (fderiv ℝ m.g.field) m.point
      (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.chain) =
      fderiv ℝ m.g.field m.point (WithLp.toLp 2 ![0, 0, z2, z3]) +
        d • WithLp.toLp 2 m.chain := by
    rw [hB, hJ]
    ext i
    fin_cases i <;>
      simp [Model.jac, VSM.jacobian, Model.tangent, Model.chain, hy2, hy3, hz2, hz3, hc1, hd, hc,
        hs, habs, Network.c0, Network.Dline]
    · linear_combination (norm := skip) (-(4 * m.g.E ^ 2 * m.g.L ^ 3 * m.g.R * m.g.X *
        (m.g.R ^ 2 - m.g.X ^ 2) * (m.g.E ^ 2 * m.g.R - P * (m.g.R ^ 2 + m.g.X ^ 2)) *
        (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 - m.g.E ^ 2 * m.g.L ^ 2 * m.g.X *
          (3 * m.g.R ^ 2 - m.g.X ^ 2))) / (m.g.M * n ^ 2 * (m.g.R ^ 2 + m.g.X ^ 2) ^ 9)) * hk +
        (-(4 * m.g.E ^ 2 * m.g.L ^ 3 * m.g.R * m.g.X * (m.g.R ^ 2 - m.g.X ^ 2) *
          (m.g.E ^ 2 * m.g.R - P * (m.g.R ^ 2 + m.g.X ^ 2))) /
          (m.g.M * n ^ 2 * (m.g.R ^ 2 + m.g.X ^ 2) ^ 8)) * hnv
      field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
  refine ⟨?_, ?_⟩
  · rw [h.coeffA_eq hy, hc1]; ring
  · rw [h.coeffB_eq hy hz, hd]

/-- **The chain exists at the Bogdanov–Takens point.** At a fold `K = 0` with the damping
`D = D_line` (`M, L ≠ 0`, `|Z|² > 0`, `E V ≠ 0`, `n ≠ 0`), the Jordan chain `(q₀, q₁)` of
`Model.jordan_chain_of_bt` completes to a normalised chain: the left null vector is
`p₁ = (D_line, M, L E (X sin δ* − R cos δ*)/|Z|², 0)/n` and `p₀` exists
(`IsBTChain.exists_of_left`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.exists_isBTChain_of_bt (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hV : m.g.E * m.g.V ≠ 0) (hK : m.K = 0)
    (hD : m.g.D = m.g.Dline) (hn : m.g.btInertia ≠ 0) :
    ∃ p₀ p₁ : State 4, IsBTChain (fderiv ℝ m.g.field m.point) (WithLp.toLp 2 m.tangent)
      (WithLp.toLp 2 m.chain) p₀ p₁ := by
  obtain ⟨k, hc, hs, hk⟩ := m.fold_coords hZ hV hK
  have hZ' : m.g.R ^ 2 + m.g.X ^ 2 ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = m.g.btInertia := ⟨_, rfl⟩
  rw [← hn_def] at hn
  have hnv : n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 = m.g.M * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 +
      m.g.E ^ 2 * m.g.L ^ 2 * m.g.X * (3 * m.g.R ^ 2 - m.g.X ^ 2) := by
    rw [hn_def, btInertia, habs]
    field_simp
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im =
      m.g.E ^ 2 * m.g.X / (m.g.R ^ 2 + m.g.X ^ 2) := by
    have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
    have h2 : m.g.syncCoeff m.δ = 0 := hK
    rw [h2, zero_add] at h1
    exact h1
  obtain ⟨hq₀, hq₁, -, hker⟩ := m.jordan_chain_of_bt hM hL hZ hK hD
  have hJ : ∀ v : Fin 4 → ℝ, fderiv ℝ m.g.field m.point (WithLp.toLp 2 v) =
      WithLp.toLp 2 (m.jac *ᵥ v) := fun v => by
    rw [m.fderiv_point, Matrix.toEuclideanCLM_toLp]
  set p := ![m.g.Dline / n, m.g.M / n, m.g.L * m.g.E * k / ((m.g.R ^ 2 + m.g.X ^ 2) * n), 0]
  have hp : p ᵥ* m.jac = 0 := by
    funext j
    fin_cases j <;>
      simp [p, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Model.jac, VSM.jacobian, hQ, hc,
        hs, hD]
    · linear_combination (norm := skip)
        (-(m.g.E ^ 2 * m.g.X) / (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 2)) * hk
      field_simp
      ring
    all_goals field_simp
    all_goals ring
  have h0 : fderiv ℝ m.g.field m.point (WithLp.toLp 2 m.tangent) = 0 := by rw [hJ, hq₀]; rfl
  have h1 : fderiv ℝ m.g.field m.point (WithLp.toLp 2 m.chain) = WithLp.toLp 2 m.tangent := by
    rw [hJ, hq₁]
  have hker' : ∀ v, fderiv ℝ m.g.field m.point v = 0 →
      ∃ s : ℝ, v = s • WithLp.toLp 2 m.tangent := fun v hv => by
    refine ⟨v 0, ?_⟩
    rw [m.fderiv_point] at hv
    have hv' : m.jac *ᵥ v.ofLp = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa using this
    have := hker _ hv'
    ext i
    exact congrFun this i
  have hpl : ∀ v, ⟪(WithLp.toLp 2 p : State 4), fderiv ℝ m.g.field m.point v⟫ = 0 := fun v => by
    rw [m.fderiv_point, Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec, hp,
      zero_dotProduct]
  have hnorm : ⟪(WithLp.toLp 2 p : State 4), WithLp.toLp 2 m.chain⟫ = 1 := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
    simp [p, dotProduct, Fin.sum_univ_four, Model.chain, Model.tangent, hc, hs, habs]
    linear_combination (norm := skip) (m.g.E ^ 2 * m.g.L ^ 2 * m.g.X *
      (3 * m.g.R ^ 2 - m.g.X ^ 2) / (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 4)) * hk +
      (-1 / (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3)) * hnv
    field_simp
    ring
  obtain ⟨p₀, hp₀⟩ := IsBTChain.exists_of_left h0 h1 hker' hpl hnorm
  exact ⟨p₀, _, hp₀⟩

/-- **The sign of `a b` at the Bogdanov–Takens point of the dynamic line.** For a physical
lossy line (`R, X, L > 0`, `E V ≠ 0`) at a fold with a positive effective inertia `n > 0`, for
every chain as in `Model.coeff_of_bt`: `a b = (P(δ*) − c₀)² L² (R² − X²) D_line/(|Z|⁴ n³)`, so
`a b > 0` iff `X < R` and `a b < 0` iff `R < X`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem Model.coeffA_mul_coeffB_pos_iff (m : Model)
    (hM : m.g.M ≠ 0) (hL : 0 < m.g.L) (hR : 0 < m.g.R) (hX : 0 < m.g.X)
    (hV : m.g.E * m.g.V ≠ 0) (hK : m.K = 0) (hn : 0 < m.g.btInertia) {p₀ p₁ : State 4}
    (h : IsBTChain (fderiv ℝ m.g.field m.point) (WithLp.toLp 2 m.tangent)
      (WithLp.toLp 2 m.chain) p₀ p₁) :
    (0 < coeffA m.g.field m.point (WithLp.toLp 2 m.tangent) p₁ *
        coeffB m.g.field m.point (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.chain) p₀ p₁ ↔
      m.g.X < m.g.R) ∧
    (coeffA m.g.field m.point (WithLp.toLp 2 m.tangent) p₁ *
        coeffB m.g.field m.point (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.chain) p₀ p₁ < 0 ↔
      m.g.R < m.g.X) := by
  have hZ : 0 < m.g.absSq := by unfold Network.absSq; positivity
  obtain ⟨ha, hb⟩ := m.coeff_of_bt hM hL.ne' hZ hV hK hn.ne' h
  have hA : m.g.A ≠ 0 := div_ne_zero hV (Real.sqrt_pos.mpr hZ).ne'
  have hcos : Real.cos (m.δ - m.g.α) = 0 :=
    (mul_eq_zero.mp (show m.g.A * Real.cos (m.δ - m.g.α) = 0 from hK)).resolve_left hA
  have hP : 0 < (m.g.qssPower m.δ - m.g.c0) ^ 2 := by
    rw [m.g.qssPower_eq_polar hZ, add_sub_cancel_left, mul_pow,
      show Real.sin (m.δ - m.g.α) ^ 2 = 1 by
        nlinarith [Real.sin_sq_add_cos_sq (m.δ - m.g.α)], mul_one]
    positivity
  have hDl : 0 < m.g.Dline := m.g.Dline_pos hR (left_ne_zero_of_mul hV) hX hL
  have hab : coeffA m.g.field m.point (WithLp.toLp 2 m.tangent) p₁ *
      coeffB m.g.field m.point (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.chain) p₀ p₁ =
      (m.g.R ^ 2 - m.g.X ^ 2) * ((m.g.qssPower m.δ - m.g.c0) ^ 2 * m.g.L ^ 2 * m.g.Dline /
        (m.g.absSq ^ 2 * m.g.btInertia ^ 3)) := by
    rw [ha, hb]; field_simp
  have hpos : 0 < (m.g.qssPower m.δ - m.g.c0) ^ 2 * m.g.L ^ 2 * m.g.Dline /
      (m.g.absSq ^ 2 * m.g.btInertia ^ 3) := by positivity
  rw [hab, mul_pos_iff_of_pos_right hpos, sub_pos]
  have hneg : (m.g.R ^ 2 - m.g.X ^ 2) * ((m.g.qssPower m.δ - m.g.c0) ^ 2 * m.g.L ^ 2 *
      m.g.Dline / (m.g.absSq ^ 2 * m.g.btInertia ^ 3)) < 0 ↔ m.g.R ^ 2 - m.g.X ^ 2 < 0 :=
    ⟨fun h2 => by nlinarith, fun h2 => by nlinarith⟩
  rw [hneg, sub_neg]
  constructor
  · constructor
    · intro h2; nlinarith
    · intro h2; nlinarith
  · constructor
    · intro h2; nlinarith
    · intro h2; nlinarith

end VSM
end powerlib.GFM.Line
