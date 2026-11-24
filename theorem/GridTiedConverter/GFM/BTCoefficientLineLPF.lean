import theorem.GridTiedConverter.GFM.BifurcationLineLPF
import theorem.GridTiedConverter.GFM.BTCoefficientLine

/-! # The Bogdanov–Takens coefficients of the VSM with a power filter on a dynamic R–L line

Kuznetsov's normal-form coefficients `a`, `b` of the double zero eigenvalue of the five-state
VSM + power filter on a dynamic line at its Bogdanov–Takens point (a fold `K = 0` with
`D = D_line`), in closed form, the counterpart of
`theorem/GridTiedConverter/GFM/BTCoefficientLine.lean` (four states).

Model boundary.
The five-state model `Line.VSMLPF` of `theorem/GridTiedConverter/GFM/Line/Model.lean`,
unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid dq frame at `ω₀`, `δ̇ = ω`,
`M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`,
export-positive active power, constant `E`; no voltage loop, inner loops, LC filter, limiting,
PLL, delay or PWM. A model `Line.VSMLPF.Model` is read at `(δ*, 0, P_ref, i_s(δ*))`; `P(δ*)` is
the quasi-steady power there, `c₀ = E² R/|Z|²`, `D_line = 2 E² R X L/|Z|⁴`; the Jordan chain is
`q₀ = (1, 0, 0, i_s'(δ*))`, `q₁ = (0, 1, −D, w)` of `Line.VSMLPF.Model.jordan_chain_of_bt`
(`theorem/GridTiedConverter/GFM/BifurcationLineLPF.lean`). Level: Kuznetsov's projection
formulas from the first and second `fderiv` of the field at the operating point; no normal-form
transformation, unfolding or criticality is asserted and no family is defined: every result is
static evidence on the model.

Source: GFM counterpart study, note t3-bifurcation (b) (the BT point with a filter at the same
`D_BT`, its coefficients and the sign of `a b` computed numerically, script s2b); the closed
forms below were derived for this module and checked with exact rational arithmetic on 24
parameter sets (scratch notes outside the repository); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed., 2004), §8.4 and §8.7.

Results.
* `Line.VSMLPF.fderiv_fderiv_field`: the second derivative of the field at every state,
  `B(u, v) = (0, 0, ω_c (−P_e u₀v₀ − E sin δ (u₀v₃ + u₃v₀) + E cos δ (u₀v₄ + u₄v₀)),
  −E cos δ u₀v₀/L, −E sin δ u₀v₀/L)`.
* The effective inertia `n₅ = n + D_line/ω_c` (`Line.VSMLPF.btInertia`, `n = VSM.btInertia`).
* `Line.VSMLPF.Model.coeff_of_bt`: at a fold with `D = D_line` (`n₅ ≠ 0`), for every normalised
  chain extending `(q₀, q₁)`, `a = (P(δ*) − c₀)/(2 n₅)` and
  `b = (P(δ*) − c₀) (2 L² (R² − X²) D_line/|Z|⁴ − M/ω_c)/n₅²`; substituting `L = 0` in these
  formulas (`n₅ = M`, `D_line = 0`) gives the quasi-static corner values `(P − c₀)/(2M)` and
  `−(P − c₀)/(M ω_c)` of `theorem/GridTiedConverter/GFM/BTCoefficient.lean` (no limit `L → 0` of
  the model is formalized).
* `Line.VSMLPF.Model.exists_isBTChain_of_bt`: the chain exists, with
  `p₁ = (D_line, M, −1/ω_c, L E (X sin δ* − R cos δ*)/|Z|², 0)/n₅`.
* `Line.VSMLPF.Model.coeffA_mul_coeffB_pos_iff`: for `n₅ > 0`, `a b > 0` iff
  `M/ω_c < 2 L² (R² − X²) D_line/|Z|⁴` and `a b < 0` iff the reverse strict inequality holds
  (the right side is `≤ 0` when `R ≤ X` and `D_line ≥ 0`, so then `a b < 0` for `M/ω_c > 0`).
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)
open powerlib.NormalForm.BogdanovTakens

namespace VSMLPF

variable (g : VSMLPF)

/-- The second derivative of the five-state field at a state `x`:
`B(u, v) = (0, 0, ω_c (−P_e u₀v₀ − E sin δ (u₀v₃ + u₃v₀) + E cos δ (u₀v₄ + u₄v₀)),
−E cos δ u₀v₀/L, −E sin δ u₀v₀/L)`, `δ = x₀`, `P_e = P_e(x)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_fderiv_field (x u v : State 5) :
    fderiv ℝ (fderiv ℝ g.field) x u v = WithLp.toLp 2 ![0, 0,
      g.ωc * (-(g.power (x 0) (x 3) (x 4) * u 0 * v 0) -
        g.E * Real.sin (x 0) * (u 0 * v 3 + u 3 * v 0) +
        g.E * Real.cos (x 0) * (u 0 * v 4 + u 4 * v 0)),
      -(g.E * Real.cos (x 0)) * u 0 * v 0 / g.L, -(g.E * Real.sin (x 0)) * u 0 * v 0 / g.L] := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ g.field) x :=
    ((g.contDiff_field (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x
  rw [fderiv_fderiv_apply hdiff, show fderiv ℝ g.field = fun y => Matrix.toEuclideanCLM
    (n := Fin 5) (𝕜 := ℝ) (g.jacobian (y 0) (y 3) (y 4)) from funext g.fderiv_field]
  set P := g.power (x 0) (x 3) (x 4)
  set c := Real.cos (x 0)
  set s := Real.sin (x 0)
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x (hasFDerivAt_coord 0 x)
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x (hasFDerivAt_coord 0 x)
  have hG : HasFDerivAt
      (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
        (g.jacobian (y 0) (y 3) (y 4)) v)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
        !![0, 0, 0, 0, 0;
          0, 0, 0, 0, 0;
          g.ωc * (-(P * v 0) - g.E * s * v 3 + g.E * c * v 4), 0, 0, -(g.ωc * (g.E * s * v 0)),
            g.ωc * (g.E * c * v 0);
          -(g.E * c * v 0) / g.L, 0, 0, 0, 0;
          -(g.E * s * v 0) / g.L, 0, 0, 0, 0]) x := by
    refine hasFDerivAt_toEuclideanCLM_of_components _
      ![0, 0, (g.ωc * (-(P * v 0) - g.E * s * v 3 + g.E * c * v 4)) • coord 0 +
          (-(g.ωc * (g.E * s * v 0))) • coord 3 + (g.ωc * (g.E * c * v 0)) • coord 4,
        (-(g.E * c * v 0) / g.L) • coord 0, (-(g.E * s * v 0) / g.L) • coord 0]
      (fun i => ?_) (fun i w => ?_)
    · fin_cases i
      · show HasFDerivAt (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 0) 0 x
        have : (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 0) = fun _ => v 1 := by
          funext y; simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_five]
        rw [this]; exact hasFDerivAt_const _ _
      · show HasFDerivAt (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 1) 0 x
        have : (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 1) = fun _ => -g.D / g.M * v 1 + -1 / g.M * v 2 := by
          funext y; simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_five]
        rw [this]; exact hasFDerivAt_const _ _
      · show HasFDerivAt (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 2) _ x
        have h3 := hasFDerivAt_coord 3 x
        have h4 := hasFDerivAt_coord 4 x
        have h := (((((((hs.mul h3).sub (hc.mul h4)).const_mul g.E).mul_const (v 0)).neg.sub_const
          (v 2)).add ((hc.const_mul g.E).mul_const (v 3))).add
          ((hs.const_mul g.E).mul_const (v 4))).const_mul g.ωc
        convert h using 1
        · funext y
          simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_five,
            Network.reactive_eq]
          ring
        · ext w
          simp [P, Network.power_eq]
          ring
      · show HasFDerivAt (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 3) _ x
        have h := ((((hs.const_mul g.E).neg.mul_const (v 0)).sub_const (g.R * v 3)).add_const
          (g.X * v 4)).mul_const g.L⁻¹
        convert h using 1
        · funext y
          simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_five]
          ring
        · ext w
          simp
          ring
      · show HasFDerivAt (fun y : State 5 => Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
            (g.jacobian (y 0) (y 3) (y 4)) v 4) _ x
        have h := ((((hc.const_mul g.E).mul_const (v 0)).sub_const (g.X * v 3)).sub_const
          (g.R * v 4)).mul_const g.L⁻¹
        convert h using 1
        · funext y
          simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_five]
          ring
        · ext w
          simp
          ring
    · fin_cases i <;> simp [Fin.sum_univ_five]
  rw [hG.fderiv]
  ext i
  fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_five] <;> ring

/-- The effective inertia of the Bogdanov–Takens point with a power filter,
`n₅ = n + D_line/ω_c` (`n = VSM.btInertia`): the normalisation of the left null vector
`(D_line ω_c, M ω_c, −1, ω_c L E (X sin δ − R cos δ)/|Z|², 0)` at a fold. -/
def btInertia : ℝ := g.toVSM.btInertia + g.Dline / g.ωc

/-- **The Bogdanov–Takens coefficients with a power filter.** At a fold `K = 0` with
`D = D_line` (`M, ω_c, L ≠ 0`, `|Z|² > 0`, `E V ≠ 0`, `n₅ = btInertia ≠ 0`), for every normalised
chain extending the Jordan chain `(q₀, q₁)` of `Model.jordan_chain_of_bt` (one exists,
`Model.exists_isBTChain_of_bt`): `a = (P(δ*) − c₀)/(2 n₅)` and
`b = (P(δ*) − c₀) (2 L² (R² − X²) D_line/|Z|⁴ − M/ω_c)/n₅²`. Substituting `L = 0` in these
formulas gives the quasi-static corner values `(P − c₀)/(2M)`, `−(P − c₀)/(M ω_c)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.coeff_of_bt (m : Model) (hM : m.g.M ≠ 0)
    (hω : m.g.ωc ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hV : m.g.E * m.g.V ≠ 0)
    (hK : m.K = 0) (hD : m.g.D = m.g.Dline) (hn : m.g.btInertia ≠ 0) {p₀ p₁ : State 5}
    (h : IsBTChain (fderiv ℝ m.g.field m.point) (WithLp.toLp 2 m.btTangent)
      (WithLp.toLp 2 m.btChain) p₀ p₁) :
    coeffA m.g.field m.point (WithLp.toLp 2 m.btTangent) p₁ =
        (m.g.qssPower m.δ - m.g.c0) / (2 * m.g.btInertia) ∧
      coeffB m.g.field m.point (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.btChain) p₀ p₁ =
        (m.g.qssPower m.δ - m.g.c0) * (2 * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) * m.g.Dline /
          m.g.absSq ^ 2 - m.g.M / m.g.ωc) / m.g.btInertia ^ 2 := by
  obtain ⟨k, hc, hs, hk⟩ := (⟨m.g.toVSM, m.δ⟩ : VSM.Model).fold_coords hZ hV hK
  have hZ' : m.g.R ^ 2 + m.g.X ^ 2 ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = m.g.btInertia := ⟨_, rfl⟩
  rw [← hn_def] at hn ⊢
  have hnv : n * m.g.ωc * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 = m.g.ωc * (m.g.M *
      (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 + m.g.E ^ 2 * m.g.L ^ 2 * m.g.X * (3 * m.g.R ^ 2 - m.g.X ^ 2)) +
      2 * m.g.E ^ 2 * m.g.R * m.g.X * m.g.L * (m.g.R ^ 2 + m.g.X ^ 2) := by
    rw [hn_def, btInertia, VSM.btInertia, Network.Dline, habs]
    field_simp
  set P := m.g.qssPower m.δ with hP
  obtain ⟨t3, ht3⟩ : ∃ t : ℝ, t = m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) /
      m.g.absSq := ⟨_, rfl⟩
  obtain ⟨t4, ht4⟩ : ∃ t : ℝ, t = m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) /
      m.g.absSq := ⟨_, rfl⟩
  obtain ⟨w3, hw3⟩ : ∃ w : ℝ, w = -(m.g.L * (m.g.R * t3 + m.g.X * t4)) / m.g.absSq :=
    ⟨_, rfl⟩
  obtain ⟨w4, hw4⟩ : ∃ w : ℝ, w = m.g.L * (m.g.X * t3 - m.g.R * t4) / m.g.absSq := ⟨_, rfl⟩
  have hT : m.btTangent = ![1, 0, 0, t3, t4] := by
    rw [ht3, ht4]; funext i; fin_cases i <;> rfl
  have hC : m.btChain = ![0, 1, -m.g.D, w3, w4] := by
    rw [hw3, hw4, ht3, ht4]; funext i; fin_cases i <;> rfl
  rw [hT, hC] at h ⊢
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = (P - m.g.c0) / n := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (P - m.g.c0) * (2 * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) *
      m.g.Dline / m.g.absSq ^ 2 - m.g.M / m.g.ωc) / n ^ 2 := ⟨_, rfl⟩
  obtain ⟨y3, hy3⟩ : ∃ y : ℝ, y = -(m.g.L * (m.g.R * (-(m.g.E * Real.cos m.δ) / m.g.L -
      c1 * w3) + m.g.X * (-(m.g.E * Real.sin m.δ) / m.g.L - c1 * w4))) / m.g.absSq := ⟨_, rfl⟩
  obtain ⟨y4, hy4⟩ : ∃ y : ℝ, y = m.g.L * (m.g.X * (-(m.g.E * Real.cos m.δ) / m.g.L -
      c1 * w3) - m.g.R * (-(m.g.E * Real.sin m.δ) / m.g.L - c1 * w4)) / m.g.absSq := ⟨_, rfl⟩
  obtain ⟨z3, hz3⟩ : ∃ z : ℝ, z = -(m.g.L * (m.g.R * (y3 - d * w3) +
      m.g.X * (y4 - d * w4))) / m.g.absSq := ⟨_, rfl⟩
  obtain ⟨z4, hz4⟩ : ∃ z : ℝ, z = m.g.L * (m.g.X * (y3 - d * w3) -
      m.g.R * (y4 - d * w4)) / m.g.absSq := ⟨_, rfl⟩
  have hpt : ∀ i, m.point i =
      ![m.δ, 0, m.g.Pref, (m.g.is m.δ).re, (m.g.is m.δ).im] i := fun i => by
    fin_cases i <;> rfl
  have hB : ∀ u v : State 5, fderiv ℝ (fderiv ℝ m.g.field) m.point u v = WithLp.toLp 2 ![0, 0,
      m.g.ωc * (-(P * u 0 * v 0) - m.g.E * Real.sin m.δ * (u 0 * v 3 + u 3 * v 0) +
        m.g.E * Real.cos m.δ * (u 0 * v 4 + u 4 * v 0)),
      -(m.g.E * Real.cos m.δ) * u 0 * v 0 / m.g.L,
      -(m.g.E * Real.sin m.δ) * u 0 * v 0 / m.g.L] := fun u v => by
    rw [fderiv_fderiv_field, hpt 0, hpt 3, hpt 4]; rfl
  have hJ : ∀ v : Fin 5 → ℝ, fderiv ℝ m.g.field m.point (WithLp.toLp 2 v) =
      WithLp.toLp 2 (m.jac *ᵥ v) := fun v => by
    rw [m.fderiv_point, Matrix.toEuclideanCLM_toLp]
  have hy : fderiv ℝ (fderiv ℝ m.g.field) m.point (WithLp.toLp 2 ![1, 0, 0, t3, t4])
      (WithLp.toLp 2 ![1, 0, 0, t3, t4]) =
      fderiv ℝ m.g.field m.point (WithLp.toLp 2 ![0, 0, m.g.M * c1, y3, y4]) +
        c1 • WithLp.toLp 2 ![0, 1, -m.g.D, w3, w4] := by
    rw [hB, hJ]
    ext i
    fin_cases i <;>
      simp [Model.jac, VSMLPF.jacobian, hy3, hy4, hw3, hw4, ht3, ht4, hc1, hc, hs, habs,
        Network.c0, hD, Network.Dline]
    · field_simp
      ring
    · linear_combination (norm := skip) (m.g.E ^ 2 * m.g.ωc * (m.g.L ^ 2 * m.g.X *
        (3 * m.g.R ^ 2 - m.g.X ^ 2) * (P * (m.g.R ^ 2 + m.g.X ^ 2) - m.g.E ^ 2 * m.g.R) +
        n * m.g.R * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3) / (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 5)) * hk +
        ((m.g.E ^ 2 * m.g.R - P * (m.g.R ^ 2 + m.g.X ^ 2)) /
          (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 4)) * hnv
      field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
  have hz : WithLp.toLp 2 ![0, 0, m.g.M * c1, y3, y4] + fderiv ℝ (fderiv ℝ m.g.field) m.point
      (WithLp.toLp 2 ![1, 0, 0, t3, t4]) (WithLp.toLp 2 ![0, 1, -m.g.D, w3, w4]) =
      fderiv ℝ m.g.field m.point (WithLp.toLp 2 ![0, 0, m.g.M * d, z3, z4]) +
        d • WithLp.toLp 2 ![0, 1, -m.g.D, w3, w4] := by
    rw [hB, hJ]
    ext i
    fin_cases i <;>
      simp [Model.jac, VSMLPF.jacobian, hy3, hy4, hz3, hz4, hw3, hw4, ht3, ht4, hc1, hd, hc,
        hs, habs, Network.c0, hD, Network.Dline]
    · field_simp
      ring
    · linear_combination (norm := skip) (m.g.E ^ 2 * m.g.L ^ 2 * m.g.X *
        (m.g.E ^ 2 * m.g.R - P * (m.g.R ^ 2 + m.g.X ^ 2)) *
        (-(4 * m.g.E ^ 2 * m.g.L ^ 3 * m.g.R * m.g.X * m.g.ωc * (m.g.R ^ 2 - m.g.X ^ 2) *
          (3 * m.g.R ^ 2 - m.g.X ^ 2)) + 4 * m.g.L * m.g.R * n * m.g.ωc *
          (m.g.R ^ 2 - m.g.X ^ 2) * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 +
          m.g.M * (m.g.R ^ 2 + m.g.X ^ 2) ^ 4 * (3 * m.g.R ^ 2 - m.g.X ^ 2)) /
        (n ^ 2 * (m.g.R ^ 2 + m.g.X ^ 2) ^ 9)) * hk +
        ((m.g.E ^ 2 * m.g.R - P * (m.g.R ^ 2 + m.g.X ^ 2)) *
          (4 * m.g.E ^ 2 * m.g.L ^ 3 * m.g.R * m.g.X * m.g.ωc * (m.g.R ^ 2 - m.g.X ^ 2) -
            m.g.M * (m.g.R ^ 2 + m.g.X ^ 2) ^ 4) /
          (n ^ 2 * m.g.ωc * (m.g.R ^ 2 + m.g.X ^ 2) ^ 8)) * hnv
      field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
  refine ⟨?_, ?_⟩
  · rw [h.coeffA_eq hy, hc1]; ring
  · rw [h.coeffB_eq hy hz, hd]

/-- **The chain exists at the Bogdanov–Takens point with a power filter.** At a fold `K = 0`
with `D = D_line` (`M, ω_c, L ≠ 0`, `|Z|² > 0`, `E V ≠ 0`, `n₅ ≠ 0`), the Jordan chain of
`Model.jordan_chain_of_bt` completes to a normalised chain, with the left null vector
`p₁ = (D_line, M, −1/ω_c, L E (X sin δ* − R cos δ*)/|Z|², 0)/n₅`
(`IsBTChain.exists_of_left`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.exists_isBTChain_of_bt (m : Model) (hM : m.g.M ≠ 0)
    (hω : m.g.ωc ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hV : m.g.E * m.g.V ≠ 0)
    (hK : m.K = 0) (hD : m.g.D = m.g.Dline) (hn : m.g.btInertia ≠ 0) :
    ∃ p₀ p₁ : State 5, IsBTChain (fderiv ℝ m.g.field m.point) (WithLp.toLp 2 m.btTangent)
      (WithLp.toLp 2 m.btChain) p₀ p₁ := by
  obtain ⟨k, hc, hs, hk⟩ := (⟨m.g.toVSM, m.δ⟩ : VSM.Model).fold_coords hZ hV hK
  have hZ' : m.g.R ^ 2 + m.g.X ^ 2 ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = m.g.btInertia := ⟨_, rfl⟩
  rw [← hn_def] at hn
  have hnv : n * m.g.ωc * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 = m.g.ωc * (m.g.M *
      (m.g.R ^ 2 + m.g.X ^ 2) ^ 3 + m.g.E ^ 2 * m.g.L ^ 2 * m.g.X * (3 * m.g.R ^ 2 - m.g.X ^ 2)) +
      2 * m.g.E ^ 2 * m.g.R * m.g.X * m.g.L * (m.g.R ^ 2 + m.g.X ^ 2) := by
    rw [hn_def, btInertia, VSM.btInertia, Network.Dline, habs]
    field_simp
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im =
      m.g.E ^ 2 * m.g.X / (m.g.R ^ 2 + m.g.X ^ 2) := by
    have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
    have h2 : m.g.syncCoeff m.δ = 0 := hK
    rw [h2, zero_add] at h1
    exact h1
  obtain ⟨hq₀, hq₁, -, -⟩ := m.jordan_chain_of_bt hM hL hZ hK hD
  have hJ : ∀ v : Fin 5 → ℝ, fderiv ℝ m.g.field m.point (WithLp.toLp 2 v) =
      WithLp.toLp 2 (m.jac *ᵥ v) := fun v => by
    rw [m.fderiv_point, Matrix.toEuclideanCLM_toLp]
  set p := ![m.g.Dline / n, m.g.M / n, -1 / (m.g.ωc * n),
    m.g.L * m.g.E * k / ((m.g.R ^ 2 + m.g.X ^ 2) * n), 0]
  have hp : p ᵥ* m.jac = 0 := by
    funext j
    fin_cases j <;>
      simp [p, Matrix.vecMul, dotProduct, Fin.sum_univ_five, Model.jac, VSMLPF.jacobian, hQ,
        hc, hs, hD]
    · linear_combination (norm := skip)
        (-(m.g.E ^ 2 * m.g.X) / (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 2)) * hk
      field_simp
      ring
    all_goals field_simp
    all_goals ring
  have ht3 : m.btTangent 3 = m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) /
      m.g.absSq := rfl
  have ht4 : m.btTangent 4 = m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) /
      m.g.absSq := rfl
  have hw : m.btChain = ![0, 1, -m.g.D,
      -(m.g.L * (m.g.R * m.btTangent 3 + m.g.X * m.btTangent 4)) / m.g.absSq,
      m.g.L * (m.g.X * m.btTangent 3 - m.g.R * m.btTangent 4) / m.g.absSq] := by
    funext i; fin_cases i <;> rfl
  have h0 : fderiv ℝ m.g.field m.point (WithLp.toLp 2 m.btTangent) = 0 := by
    rw [hJ, hq₀]; rfl
  have h1 : fderiv ℝ m.g.field m.point (WithLp.toLp 2 m.btChain) =
      WithLp.toLp 2 m.btTangent := by
    rw [hJ, hq₁]
  have hker : ∀ v, fderiv ℝ m.g.field m.point v = 0 →
      ∃ s : ℝ, v = s • WithLp.toLp 2 m.btTangent := fun v hv => by
    refine ⟨v 0, ?_⟩
    rw [m.fderiv_point] at hv
    have hv' : m.jac *ᵥ v.ofLp = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa using this
    have := m.eq_smul_btTangent_of_mulVec_eq_zero hM hL hZ hv'
    ext i
    exact congrFun this i
  have hpl : ∀ v, ⟪(WithLp.toLp 2 p : State 5), fderiv ℝ m.g.field m.point v⟫ = 0 := fun v => by
    rw [m.fderiv_point, Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec, hp,
      zero_dotProduct]
  have hnorm : ⟪(WithLp.toLp 2 p : State 5), WithLp.toLp 2 m.btChain⟫ = 1 := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hw]
    simp [p, dotProduct, Fin.sum_univ_five, ht3, ht4, hc, hs, habs, hD, Network.Dline]
    linear_combination (norm := skip) (m.g.E ^ 2 * m.g.L ^ 2 * m.g.X *
      (3 * m.g.R ^ 2 - m.g.X ^ 2) / (n * (m.g.R ^ 2 + m.g.X ^ 2) ^ 4)) * hk +
      (-1 / (n * m.g.ωc * (m.g.R ^ 2 + m.g.X ^ 2) ^ 3)) * hnv
    field_simp
    ring
  obtain ⟨p₀, hp₀⟩ := IsBTChain.exists_of_left h0 h1 hker hpl hnorm
  exact ⟨p₀, _, hp₀⟩

/-- **The sign of `a b` with a power filter.** At a fold (`M, ω_c, L ≠ 0`, `|Z|² > 0`,
`E V ≠ 0`, `D = D_line`) with `n₅ > 0`, for every chain as in `Model.coeff_of_bt`:
`a b = (P(δ*) − c₀)² (2 L² (R² − X²) D_line/|Z|⁴ − M/ω_c)/(2 n₅³)`, so `a b > 0` iff
`M/ω_c < 2 L² (R² − X²) D_line/|Z|⁴` and `a b < 0` iff the reverse strict inequality holds (the
right side is `≤ 0` when `R ≤ X` and `D_line ≥ 0`). Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.coeffA_mul_coeffB_pos_iff (m : Model)
    (hM : m.g.M ≠ 0) (hω : m.g.ωc ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq)
    (hV : m.g.E * m.g.V ≠ 0) (hK : m.K = 0) (hD : m.g.D = m.g.Dline) (hn : 0 < m.g.btInertia)
    {p₀ p₁ : State 5}
    (h : IsBTChain (fderiv ℝ m.g.field m.point) (WithLp.toLp 2 m.btTangent)
      (WithLp.toLp 2 m.btChain) p₀ p₁) :
    (0 < coeffA m.g.field m.point (WithLp.toLp 2 m.btTangent) p₁ *
        coeffB m.g.field m.point (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.btChain) p₀ p₁ ↔
      m.g.M / m.g.ωc < 2 * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) * m.g.Dline / m.g.absSq ^ 2) ∧
    (coeffA m.g.field m.point (WithLp.toLp 2 m.btTangent) p₁ *
        coeffB m.g.field m.point (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.btChain) p₀ p₁ < 0 ↔
      2 * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) * m.g.Dline / m.g.absSq ^ 2 < m.g.M / m.g.ωc) := by
  obtain ⟨ha, hb⟩ := m.coeff_of_bt hM hω hL hZ hV hK hD hn.ne' h
  have hA : m.g.A ≠ 0 := div_ne_zero hV (Real.sqrt_pos.mpr hZ).ne'
  have hcos : Real.cos (m.δ - m.g.α) = 0 :=
    (mul_eq_zero.mp (show m.g.A * Real.cos (m.δ - m.g.α) = 0 from hK)).resolve_left hA
  have hP : 0 < (m.g.qssPower m.δ - m.g.c0) ^ 2 := by
    rw [m.g.qssPower_eq_polar hZ, add_sub_cancel_left, mul_pow,
      show Real.sin (m.δ - m.g.α) ^ 2 = 1 by
        nlinarith [Real.sin_sq_add_cos_sq (m.δ - m.g.α)], mul_one]
    positivity
  set B' := 2 * m.g.L ^ 2 * (m.g.R ^ 2 - m.g.X ^ 2) * m.g.Dline / m.g.absSq ^ 2 -
    m.g.M / m.g.ωc with hB'
  have hab : coeffA m.g.field m.point (WithLp.toLp 2 m.btTangent) p₁ *
      coeffB m.g.field m.point (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.btChain) p₀ p₁ =
      B' * ((m.g.qssPower m.δ - m.g.c0) ^ 2 / (2 * m.g.btInertia ^ 3)) := by
    rw [ha, hb, hB']; field_simp
  have hpos : 0 < (m.g.qssPower m.δ - m.g.c0) ^ 2 / (2 * m.g.btInertia ^ 3) := by positivity
  rw [hab, mul_pos_iff_of_pos_right hpos]
  have hneg : B' * ((m.g.qssPower m.δ - m.g.c0) ^ 2 / (2 * m.g.btInertia ^ 3)) < 0 ↔ B' < 0 :=
    ⟨fun h2 => by nlinarith, fun h2 => by nlinarith⟩
  rw [hneg, hB', sub_pos, sub_neg]
  exact ⟨Iff.rfl, Iff.rfl⟩

end VSMLPF
end powerlib.GFM.Line
