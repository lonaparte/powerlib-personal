import theorem.GridTiedConverter.GFM.Bifurcation
import theorem.GridTiedConverter.GFM.BifurcationLineLPF
import theorem.GridTiedConverter.GFM.Line.PSC
import theorem.Dynamics.BTUnfolding

/-! # Kuznetsov's nondegeneracy condition (BT.3) at the Bogdanov–Takens points of the GFM models

The (BT.3) map of the two-parameter unfoldings of the grid-forming models, its Jacobian matrix
from `HasFDerivAt`, and its determinant in closed form, with its sign and zero set; at every
Bogdanov–Takens point of a physical model the map is regular.

Model boundary.
* Models, unchanged: the VSM on a dynamic R–L line `Line.VSM` (state `(δ, ω, i_d, i_q)`), the VSM
  with a power filter on the line `Line.VSMLPF` (`(δ, ω, P_f, i_d, i_q)`) and power
  synchronization on the line `Line.PSC` (`(δ, i_d, i_q)`) of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, and the quasi-static lossy VSM with a power
  filter `VSMLPFLossy` (`(δ, ω, P_f)`) of `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`; their
  boundaries are those of these modules (constant `E`, no inner loops, PLL, delay, PWM, LC filter,
  limiting; export-positive power).
* Unfolding parameters: `(P_ref, D)` for `Line.VSM`, `Line.VSMLPF` and `VSMLPFLossy` (network,
  inertia and filter fixed), `(P_ref, K_p)` for `Line.PSC`; `withParams` replaces them.
* The (BT.3) map of a model with state `x ∈ ℝⁿ` is `Φ(x, α) = (f(x; α), a₀, a₁) ∈ ℝⁿ⁺²`
  (`btMap`, coordinates `(x, α)`), `a₀, a₁` the coefficients of `s⁰`, `s¹` of the characteristic
  polynomial (`Matrix.charpoly`) of the model's Jacobian matrix at `x` (`jacobian`, the `fderiv`
  of the field by `hasFDerivAt_field` of the model modules; for `VSMLPFLossy` the matrix
  `VSMLPF.jacobian (δ − α)` of `VSMLPFLossy.hasFDerivAt_field`). Regular means `DΦ` bijective. For
  `n = 2`, `a₀ = det J` and `a₁ = −tr J`, so `Φ` is Kuznetsov's map `(x, α) ↦ (f, tr J, det J)` of
  condition (BT.3) up to the order and sign of two components. For `n > 2` Kuznetsov states
  (BT.3) for the family restricted to a parameter-dependent centre manifold; the regularity of
  `Φ` is its `n`-dimensional form (near a Bogdanov–Takens point the characteristic polynomial
  factors as `(s² − τ s + Δ) q(s)` with `q(0) ≠ 0`, `(τ, Δ) ↦ (a₀, a₁) = (Δ q(0), Δ q'(0) − τ q(0))`
  is a local diffeomorphism, and on equilibria `(τ, Δ)` are the trace and determinant of the
  restricted Jacobian). That equivalence, the parameter-dependent centre manifold and normal form,
  and the bifurcation diagram are not formalized here.
* Static statements only: the map, its derivative and determinant; no flow.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., Springer, 2004), §8.4
(Theorem 8.4, the nondegeneracy conditions (BT.0)–(BT.3)) and §8.7 (Bogdanov–Takens in `n`
dimensions, reduction to the centre manifold); the Bogdanov–Takens points of
`theorem/GridTiedConverter/GFM/BifurcationLine.lean` (`K = 0`, `D = D_line`),
`theorem/GridTiedConverter/GFM/BifurcationLineLPF.lean` (same), `HopfLinePSC.lean` (`K = 0`,
`K_p D_line = 1`) and `theorem/GridTiedConverter/GFM/Bifurcation.lean` (`K = 0`, `D = 0`). The
determinants were derived with SymPy (exact; scratch scripts outside the repository, untrusted)
and are proved here by Laplace expansion.

Results.
* Characteristic polynomials at every state: `Line.VSMLPF.charpoly_jacobian`,
  `Line.PSC.charpoly_jacobian` (from the `det_characteristicMatrix` laws of the model modules;
  `Line.VSM.charpoly_jacobian` is in `theorem/GridTiedConverter/GFM/BifurcationLine.lean`);
  `Line.Network.hasFDerivAt_reactive` (`∂Q_e/∂δ = P_e`).
* The maps in closed form (`btMap_apply`), their derivatives (`hasFDerivAt_btMap`, matrix
  `btJacobian`) and the determinants at every point (`det_btJacobian`, `det_fderiv_btMap`):
  `Line.VSM`: `ρ² (R E² − |Z|² P_e)/(L² M³)`; `Line.VSMLPF`: `ω_c³ ρ² (|Z|² P_e − R E²)/(L² M³)`;
  `Line.PSC`: `2 E² K_p² R X (R E² − |Z|² P_e)/L⁵`; `VSMLPFLossy`: `ω_c³ (P(δ) − c₀)/M³`. Each
  vanishes exactly where the power equals the centre `c₀ = E² R/|Z|²` of the power-angle curve
  (and, for `Line.PSC`, on a lossless line, which has no Bogdanov–Takens point).
* At the operating point (`Model.btPoint`, the point and the model's parameters;
  `Model.det_fderiv_btMap_btPoint`): `−ρ³(P(δ*) − c₀)/M³`, `ω_c³ρ³(P(δ*) − c₀)/M³`,
  `−2E²K_p²RX|Z|²(P(δ*) − c₀)/L⁵`, `ω_c³(P(δ*) − c₀)/M³`. At a fold `K = 0`,
  `(P(δ*) − c₀)² = A²` (`Line.Network.sq_qssPower_sub_c0_of_syncCoeff_eq_zero`), so the
  determinant is `± (positive factor) · A` (`Model.det_fderiv_btMap_ne_zero_iff`: nonzero iff
  `A ≠ 0`), with its sign fixed by the side of the fold (`Model.det_fderiv_btMap_neg_iff`,
  `Model.det_fderiv_btMap_pos_iff`: the upper fold `P(δ*) = c₀ + A` against the lower).
* The Bogdanov–Takens points are zeros of the maps (`Model.btMap_btPoint_eq_zero`: balanced,
  `K = 0` and `D = D_line`, resp. `K_p D_line = 1`, resp. `D = 0`), and **(BT.3) holds there**
  (`Line.VSM.Model.bijective_fderiv_btMap`, `Line.VSMLPF.Model.bijective_fderiv_btMap` for a
  physical network; `Line.PSC.Model.bijective_fderiv_btMap` for `A ≠ 0`, the gain condition
  forcing a lossy reactive line; `VSMLPFLossy.Model.bijective_fderiv_btMap` for `M, ω_c, A ≠ 0`),
  through `Dynamics.bijective_of_det_ne_zero` (`theorem/Dynamics/BTUnfolding.lean`). The other
  conditions of Theorem 8.4 concern the Jordan block (BT.0) and the quadratic normal-form
  coefficients `a`, `b` (BT.1), (BT.2); they are computed in `BTCoefficient.lean`,
  `BTCoefficientLine.lean`, `BTCoefficientLineLPF.lean` and `HopfLinePSC.lean`. The homoclinic
  curve to leading order is the generic `NormalForm.BogdanovTakens.homoclinicCurve` of
  `theorem/Dynamics/BTUnfolding.lean`; its persistence for these models is not proved.

Family and connection conclusions.
The module defines no family and states no behaviour: every result is static evidence on the
models of the families `Line.VSM.family`, `Line.VSMLPF.family`, `Line.PSC.family` and
`VSMLPFLossy.family`.
-/

noncomputable section
namespace powerlib.GFM.Line
open Polynomial Matrix
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)

namespace Network

variable (N : Network)

/-- `∂Q_e/∂δ = P_e`, `∂Q_e/∂i_d = E sin δ`, `∂Q_e/∂i_q = −E cos δ`, read on three coordinates
of a state of any dimension. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_reactive {n : ℕ} (a b c : Fin n) (x : State n) :
    HasFDerivAt (fun y : State n => N.reactive (y a) (y b) (y c))
      ((N.power (x a) (x b) (x c)) • coord a + (N.E * Real.sin (x a)) • coord b +
        (-(N.E * Real.cos (x a))) • coord c) x := by
  have ha := hasFDerivAt_coord a x
  have hcos := (Real.hasDerivAt_cos (x a)).comp_hasFDerivAt x ha
  have hsin := (Real.hasDerivAt_sin (x a)).comp_hasFDerivAt x ha
  have h := ((hsin.mul (hasFDerivAt_coord b x)).sub
    (hcos.mul (hasFDerivAt_coord c x))).const_mul N.E
  convert h using 1
  · funext y; simp [reactive_eq]
  · ext v; simp [power_eq]; ring

/-- At a fold of the power-angle curve, `K(δ) = 0`, the power is at an extremum:
`(P(δ) − c₀)² = A²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sq_qssPower_sub_c0_of_syncCoeff_eq_zero (hZ : 0 < N.absSq)
    {δ : ℝ} (hK : N.syncCoeff δ = 0) : (N.qssPower δ - N.c0) ^ 2 = N.A ^ 2 := by
  rw [N.qssPower_eq_polar hZ]
  have hc := Real.sin_sq_add_cos_sq (δ - N.α)
  have hK' : N.A * Real.cos (δ - N.α) = 0 := hK
  linear_combination N.A ^ 2 * hc - N.A * Real.cos (δ - N.α) * hK'

end Network

namespace VSM

variable (g : VSM)

/-- The set-point and the damping replaced: the two unfolding parameters `(P_ref, D)`. -/
def withParams (P D : ℝ) : VSM := { g with Pref := P, D := D }

/-- The state `(δ, ω, i_d, i_q)` of a point `(δ, ω, i_d, i_q, P_ref, D)`. -/
def btState (z : State 6) : State 4 := WithLp.toLp 2 ![z 0, z 1, z 2, z 3]

/-- **Kuznetsov's (BT.3) map** of the unfolding in `(P_ref, D)`. -/
def btMap (z : State 6) : State 6 :=
  WithLp.toLp 2 ![(g.withParams (z 4) (z 5)).field (btState z) 0,
    (g.withParams (z 4) (z 5)).field (btState z) 1,
    (g.withParams (z 4) (z 5)).field (btState z) 2,
    (g.withParams (z 4) (z 5)).field (btState z) 3,
    ((g.withParams (z 4) (z 5)).jacobian (z 0) (z 2) (z 3)).charpoly.coeff 0,
    ((g.withParams (z 4) (z 5)).jacobian (z 0) (z 2) (z 3)).charpoly.coeff 1]

@[tmio M, powerlib_domain] theorem btMap_apply (z : State 6) :
    g.btMap z = WithLp.toLp 2 ![z 1, (z 4 - g.power (z 0) (z 2) (z 3) - z 5 * z 1) / g.M,
      g.rateD (z 0) (z 2) (z 3), g.rateQ (z 0) (z 2) (z 3),
      (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (z 0) (z 2) (z 3) * g.ρ) / g.M,
      (z 5 * g.ρ - 2 * g.σ * g.reactive (z 0) (z 2) (z 3)) / g.M] := by
  simp only [btMap, charpoly_jacobian]
  simp [coeff_X, coeff_C, withParams, field, btState, coeff0, coeff1]

/-- The Jacobian matrix of the (BT.3) map. -/
def btJacobian (z : State 6) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 0;
    g.reactive (z 0) (z 2) (z 3) / g.M, -z 5 / g.M, -(g.E * Real.cos (z 0)) / g.M,
      -(g.E * Real.sin (z 0)) / g.M, 1 / g.M, -z 1 / g.M;
    -(g.E * Real.sin (z 0)) / g.L, 0, -g.R / g.L, g.X / g.L, 0, 0;
    g.E * Real.cos (z 0) / g.L, 0, -g.X / g.L, -g.R / g.L, 0, 0;
    -(g.ρ * g.power (z 0) (z 2) (z 3)) / g.M, 0, -(g.ρ * (g.E * Real.sin (z 0))) / g.M,
      g.ρ * (g.E * Real.cos (z 0)) / g.M, 0, 0;
    -(2 * g.σ * g.power (z 0) (z 2) (z 3)) / g.M, 0,
      -(2 * g.σ * (g.E * Real.sin (z 0))) / g.M, 2 * g.σ * (g.E * Real.cos (z 0)) / g.M, 0,
      g.ρ / g.M]

@[tmio M, powerlib_domain] theorem det_btJacobian (z : State 6) :
    (g.btJacobian z).det =
      g.ρ ^ 2 * (g.R * g.E ^ 2 - g.absSq * g.power (z 0) (z 2) (z 3)) / (g.L ^ 2 * g.M ^ 3) := by
  set c := Real.cos (z 0) with hc
  set s := Real.sin (z 0) with hs
  set P := g.power (z 0) (z 2) (z 3) with hP
  set B : Matrix (Fin 5) (Fin 5) ℝ := !![0, 1, 0, 0, 0;
    -(g.E * s) / g.L, 0, -g.R / g.L, g.X / g.L, 0;
    g.E * c / g.L, 0, -g.X / g.L, -g.R / g.L, 0;
    -(g.ρ * P) / g.M, 0, -(g.ρ * (g.E * s)) / g.M, g.ρ * (g.E * c) / g.M, 0;
    -(2 * g.σ * P) / g.M, 0, -(2 * g.σ * (g.E * s)) / g.M, 2 * g.σ * (g.E * c) / g.M,
      g.ρ / g.M] with hBdef
  set C : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0;
    -(g.E * s) / g.L, 0, -g.R / g.L, g.X / g.L;
    g.E * c / g.L, 0, -g.X / g.L, -g.R / g.L;
    -(g.ρ * P) / g.M, 0, -(g.ρ * (g.E * s)) / g.M, g.ρ * (g.E * c) / g.M] with hCdef
  have hB : (g.btJacobian z).submatrix (Fin.succAbove 1) (Fin.succAbove 4) = B := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hC : B.submatrix (Fin.succAbove 4) (Fin.succAbove 4) = C := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h6 : (g.btJacobian z).det = -(1 / g.M) * B.det := by
    rw [Matrix.det_succ_column _ 4, Fin.sum_univ_six, hB]
    simp [btJacobian]
    ring
  have h5 : B.det = g.ρ / g.M * C.det := by
    rw [Matrix.det_succ_column _ 4, Fin.sum_univ_five, hC]
    simp [hBdef]
    norm_num
  have h4 : C.det = g.ρ / g.M * (P * (g.R ^ 2 + g.X ^ 2) - g.R * g.E ^ 2) / g.L ^ 2 := by
    have hD : C.submatrix Fin.succ (Fin.succAbove 1) = !![-(g.E * s) / g.L, -g.R / g.L, g.X / g.L;
        g.E * c / g.L, -g.X / g.L, -g.R / g.L;
        -(g.ρ * P) / g.M, -(g.ρ * (g.E * s)) / g.M, g.ρ * (g.E * c) / g.M] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, hD]
    simp [hCdef, Matrix.det_fin_three]
    linear_combination (-(g.ρ * g.R * g.E ^ 2) / (g.M * g.L ^ 2)) * Real.sin_sq_add_cos_sq (z 0)
  rw [h6, h5, h4, Network.absSq]
  ring

@[tmio M, powerlib_domain] theorem hasFDerivAt_btMap (z : State 6) :
    HasFDerivAt g.btMap (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) (g.btJacobian z)) z := by
  have hf : g.btMap = fun y : State 6 => WithLp.toLp 2 ![y 1,
      (y 4 - g.power (y 0) (y 2) (y 3) - y 5 * y 1) / g.M,
      g.rateD (y 0) (y 2) (y 3), g.rateQ (y 0) (y 2) (y 3),
      (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (y 0) (y 2) (y 3) * g.ρ) / g.M,
      (y 5 * g.ρ - 2 * g.σ * g.reactive (y 0) (y 2) (y 3)) / g.M] := funext g.btMap_apply
  have hP := g.hasFDerivAt_power 0 2 3 z
  have hQ := g.hasFDerivAt_reactive 0 2 3 z
  rw [hf]
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![coord 1, g.M⁻¹ • (coord 4 - ((-g.reactive (z 0) (z 2) (z 3)) • coord 0 +
        (g.E * Real.cos (z 0)) • coord 2 + (g.E * Real.sin (z 0)) • coord 3) -
        (z 5 • coord 1 + z 1 • coord 5)),
      (-(g.E * Real.sin (z 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 2 + (g.X / g.L) • coord 3,
      (g.E * Real.cos (z 0) / g.L) • coord 0 + (-g.X / g.L) • coord 2 + (-g.R / g.L) • coord 3,
      g.M⁻¹ • (-(g.ρ • ((g.power (z 0) (z 2) (z 3)) • coord 0 +
        (g.E * Real.sin (z 0)) • coord 2 + (-(g.E * Real.cos (z 0))) • coord 3))),
      g.M⁻¹ • (g.ρ • coord 5 - (2 * g.σ) • ((g.power (z 0) (z 2) (z 3)) • coord 0 +
        (g.E * Real.sin (z 0)) • coord 2 + (-(g.E * Real.cos (z 0))) • coord 3))]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · exact hasFDerivAt_coord 1 z
    · have h := ((((hasFDerivAt_coord 4 z).sub hP).sub
        ((hasFDerivAt_coord 5 z).mul (hasFDerivAt_coord 1 z))).const_smul g.M⁻¹)
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp; try ring
    · exact g.hasFDerivAt_rateD 0 2 3 z
    · exact g.hasFDerivAt_rateQ 0 2 3 z
    · have h := ((hasFDerivAt_const (g.E ^ 2 * g.X / g.L ^ 2) z).sub
        (hQ.mul_const g.ρ)).const_smul g.M⁻¹
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp; try ring
    · have h := (((hasFDerivAt_coord 5 z).mul_const g.ρ).sub
        (hQ.const_mul (2 * g.σ))).const_smul g.M⁻¹
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp; try ring
  · fin_cases i <;> (simp [btJacobian, Fin.sum_univ_six]; try ring)

/-- The determinant of the derivative of the (BT.3) map at every point. -/
@[tmio M, powerlib_domain] theorem det_fderiv_btMap (z : State 6) :
    LinearMap.det (fderiv ℝ g.btMap z : State 6 →ₗ[ℝ] State 6) =
      g.ρ ^ 2 * (g.R * g.E ^ 2 - g.absSq * g.power (z 0) (z 2) (z 3)) / (g.L ^ 2 * g.M ^ 3) := by
  rw [(g.hasFDerivAt_btMap z).fderiv, Dynamics.det_toEuclideanCLM, g.det_btJacobian z]

/-- The operating point of a model with its parameters, `(δ*, 0, i_s(δ*), P_ref, D)`. -/
def Model.btPoint (m : Model) : State 6 :=
  WithLp.toLp 2 ![m.δ, 0, (m.g.is m.δ).re, (m.g.is m.δ).im, m.g.Pref, m.g.D]

/-- The (BT.3) map reads the model at its operating point: the field there and the two lowest
coefficients `a₀ = coeff0 Q`, `a₁ = coeff1 Q`. -/
@[tmio M, powerlib_domain] theorem Model.btMap_btPoint (m : Model) :
    m.g.btMap m.btPoint = WithLp.toLp 2 ![m.g.field m.point 0, m.g.field m.point 1,
      m.g.field m.point 2, m.g.field m.point 3, m.g.coeff0 m.Q, m.g.coeff1 m.Q] := by
  rw [btMap_apply]
  simp [Model.btPoint, Model.point, qss, coeff0, coeff1, Model.Q, Network.qssReactive]

/-- At a Bogdanov–Takens point (balanced, `K = 0`, `D = D_line`) the (BT.3) map vanishes. -/
@[tmio M, powerlib_domain] theorem Model.btMap_btPoint_eq_zero (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hb : m.g.qssPower m.δ = m.g.Pref) (hK : m.K = 0)
    (hD : m.g.D = m.g.Dline) : m.g.btMap m.btPoint = 0 := by
  have hf := (m.field_point_eq_zero_iff hM hL hZ.ne').mpr hb
  rw [m.btMap_btPoint, hf, m.coeff0_eq hL hZ, m.coeff1_eq hL hZ, hK, hD]
  ext i; fin_cases i <;> simp

/-- **The (BT.3) determinant at the operating point**: `det = −ρ³ (P(δ*) − c₀)/M³`. -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_btPoint (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 6 →ₗ[ℝ] State 6) =
      -(m.g.ρ ^ 3 * (m.g.qssPower m.δ - m.g.c0) / m.g.M ^ 3) := by
  rw [det_fderiv_btMap]
  have hP : m.g.power (m.btPoint 0) (m.btPoint 2) (m.btPoint 3) = m.g.qssPower m.δ := rfl
  rw [hP]
  have hρ : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
  have hZ' := hZ.ne'
  rw [Network.c0, hρ]
  field_simp
  ring

/-- **Kuznetsov's (BT.3) at a fold of the line.** At a fold `K = 0` (in particular at every
Bogdanov–Takens point `K = 0`, `D = D_line`) the (BT.3) determinant is `∓ρ³A/M³`; it is nonzero
iff `A ≠ 0` (`M, L ≠ 0`, `|Z|² > 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_ne_zero_iff (m : Model)
    (hM : m.g.M ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 6 →ₗ[ℝ] State 6) ≠ 0 ↔
      m.g.A ≠ 0 := by
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  have hsq := m.g.sq_qssPower_sub_c0_of_syncCoeff_eq_zero hZ hK
  rw [m.det_fderiv_btMap_btPoint hL hZ, neg_ne_zero, div_ne_zero_iff, mul_ne_zero_iff,
    and_iff_right (pow_ne_zero 3 hρ), and_iff_left (pow_ne_zero 3 hM)]
  constructor
  · intro h hA; apply h; rw [hA] at hsq; simpa using hsq
  · intro hA h; apply hA; rw [h] at hsq; simpa using hsq.symm

/-- **The sign of the (BT.3) determinant** (`M > 0`, `L ≠ 0`, `|Z|² > 0`): negative exactly when the
operating power lies above the centre `c₀` of the power-angle curve; at the upper fold
`P(δ*) = c₀ + A` (the maximum) the determinant is `−ρ³A/M³ < 0`, at the lower fold `+ρ³A/M³`. -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_neg_iff (m : Model) (hM : 0 < m.g.M)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 6 →ₗ[ℝ] State 6) < 0 ↔
      m.g.c0 < m.g.qssPower m.δ := by
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (by positivity)
  rw [m.det_fderiv_btMap_btPoint hL hZ, neg_lt_zero, div_pos_iff_of_pos_right (by positivity),
    mul_pos_iff_of_pos_left (by positivity), sub_pos]

/-- **(BT.3) holds at every Bogdanov–Takens point of a physical line.** For a physical network
(`Line.Network.Physical`) and `M ≠ 0`, at a fold `K = 0` — in particular at the Bogdanov–Takens
point `K = 0`, `D = D_line` (`Line.VSM.Model.two_le_rootMultiplicity_zero_iff`) — the derivative
of the (BT.3) map `(x, P_ref, D) ↦ (f, a₀, a₁)` is bijective: Kuznetsov's transversality
condition for the unfolding in `(P_ref, D)`. -/
@[tmio M, powerlib_domain] theorem Model.bijective_fderiv_btMap (m : Model) (hp : m.g.Physical)
    (hM : m.g.M ≠ 0) (hK : m.K = 0) :
    Function.Bijective (fderiv ℝ m.g.btMap m.btPoint) := by
  have hZ := hp.absSq_pos
  have hA : m.g.A ≠ 0 := div_ne_zero (mul_pos hp.E hp.V).ne' (Real.sqrt_pos.mpr hZ).ne'
  exact Dynamics.bijective_of_det_ne_zero _
    ((m.det_fderiv_btMap_ne_zero_iff hM hp.L.ne' hZ hK).mpr hA)

end VSM

/-! ## The VSM with a power filter on the line (five states, parameters `(P_ref, D)`) -/

namespace VSMLPF

variable (g : VSMLPF)

/-- The characteristic polynomial of the Jacobian at every state. -/
@[tmio M, powerlib_domain] theorem charpoly_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).charpoly = X ^ 5 + C g.coeff4 * X ^ 4 + C g.coeff3 * X ^ 3 +
      C (g.coeff2 (g.reactive δ id iq)) * X ^ 2 + C (g.coeff1 (g.reactive δ id iq)) * X +
        C (g.coeff0 (g.reactive δ id iq)) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  apply Polynomial.funext
  intro s
  rw [← Matrix.charpoly_map, ← Linear.det_characteristicMatrix_eq_eval,
    g.det_characteristicMatrix_quintic]
  simp

/-- The set-point and the damping replaced: the unfolding parameters `(P_ref, D)`. -/
def withParams (P D : ℝ) : VSMLPF := { g with Pref := P, D := D }

/-- The state `(δ, ω, P_f, i_d, i_q)` of a point `(δ, ω, P_f, i_d, i_q, P_ref, D)`. -/
def btState (z : State 7) : State 5 := WithLp.toLp 2 ![z 0, z 1, z 2, z 3, z 4]

/-- **Kuznetsov's (BT.3) map** of the unfolding in `(P_ref, D)`:
`(δ, ω, P_f, i_d, i_q, P_ref, D) ↦ (f(x; P_ref, D), a₀, a₁)`, `a₀, a₁` the two lowest
coefficients of the characteristic polynomial of the (`fderiv`) Jacobian `VSMLPF.jacobian`. -/
def btMap (z : State 7) : State 7 :=
  WithLp.toLp 2 ![(g.withParams (z 5) (z 6)).field (btState z) 0,
    (g.withParams (z 5) (z 6)).field (btState z) 1,
    (g.withParams (z 5) (z 6)).field (btState z) 2,
    (g.withParams (z 5) (z 6)).field (btState z) 3,
    (g.withParams (z 5) (z 6)).field (btState z) 4,
    ((g.withParams (z 5) (z 6)).jacobian (z 0) (z 3) (z 4)).charpoly.coeff 0,
    ((g.withParams (z 5) (z 6)).jacobian (z 0) (z 3) (z 4)).charpoly.coeff 1]

/-- The (BT.3) map in closed form. -/
@[tmio M, powerlib_domain] theorem btMap_apply (z : State 7) :
    g.btMap z = WithLp.toLp 2 ![z 1, (z 5 - z 2 - z 6 * z 1) / g.M,
      g.ωc * (g.power (z 0) (z 3) (z 4) - z 2), g.rateD (z 0) (z 3) (z 4),
      g.rateQ (z 0) (z 3) (z 4),
      g.ωc * ((g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (z 0) (z 3) (z 4) * g.ρ) / g.M),
      g.ωc * ((z 6 * g.ρ - 2 * g.σ * g.reactive (z 0) (z 3) (z 4)) / g.M)] := by
  simp only [btMap, charpoly_jacobian]
  simp [coeff_X, coeff_C, withParams, field, btState, coeff0, coeff1, VSM.coeff0, VSM.coeff1]

/-- The Jacobian matrix of the (BT.3) map. -/
def btJacobian (z : State 7) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0, 1, 0, 0, 0, 0, 0;
    0, -z 6 / g.M, -1 / g.M, 0, 0, 1 / g.M, -z 1 / g.M;
    -(g.ωc * g.reactive (z 0) (z 3) (z 4)), 0, -g.ωc, g.ωc * (g.E * Real.cos (z 0)),
      g.ωc * (g.E * Real.sin (z 0)), 0, 0;
    -(g.E * Real.sin (z 0)) / g.L, 0, 0, -g.R / g.L, g.X / g.L, 0, 0;
    g.E * Real.cos (z 0) / g.L, 0, 0, -g.X / g.L, -g.R / g.L, 0, 0;
    -(g.ωc * (g.ρ * g.power (z 0) (z 3) (z 4))) / g.M, 0, 0,
      -(g.ωc * (g.ρ * (g.E * Real.sin (z 0)))) / g.M,
      g.ωc * (g.ρ * (g.E * Real.cos (z 0))) / g.M, 0, 0;
    -(g.ωc * (2 * g.σ * g.power (z 0) (z 3) (z 4))) / g.M, 0, 0,
      -(g.ωc * (2 * g.σ * (g.E * Real.sin (z 0)))) / g.M,
      g.ωc * (2 * g.σ * (g.E * Real.cos (z 0))) / g.M, 0, g.ωc * g.ρ / g.M]

@[tmio M, powerlib_domain] theorem hasFDerivAt_btMap (z : State 7) :
    HasFDerivAt g.btMap (Matrix.toEuclideanCLM (n := Fin 7) (𝕜 := ℝ) (g.btJacobian z)) z := by
  have hf : g.btMap = fun y : State 7 => WithLp.toLp 2 ![y 1, (y 5 - y 2 - y 6 * y 1) / g.M,
      g.ωc * (g.power (y 0) (y 3) (y 4) - y 2), g.rateD (y 0) (y 3) (y 4),
      g.rateQ (y 0) (y 3) (y 4),
      g.ωc * ((g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (y 0) (y 3) (y 4) * g.ρ) / g.M),
      g.ωc * ((y 6 * g.ρ - 2 * g.σ * g.reactive (y 0) (y 3) (y 4)) / g.M)] :=
    funext g.btMap_apply
  have hP := g.hasFDerivAt_power 0 3 4 z
  have hQ := g.hasFDerivAt_reactive 0 3 4 z
  rw [hf]
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![coord 1, g.M⁻¹ • (coord 5 - coord 2 - (z 6 • coord 1 + z 1 • coord 6)),
      g.ωc • ((-g.reactive (z 0) (z 3) (z 4)) • coord 0 + (g.E * Real.cos (z 0)) • coord 3 +
        (g.E * Real.sin (z 0)) • coord 4 - coord 2),
      (-(g.E * Real.sin (z 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 3 + (g.X / g.L) • coord 4,
      (g.E * Real.cos (z 0) / g.L) • coord 0 + (-g.X / g.L) • coord 3 + (-g.R / g.L) • coord 4,
      g.ωc • (g.M⁻¹ • (-(g.ρ • ((g.power (z 0) (z 3) (z 4)) • coord 0 +
        (g.E * Real.sin (z 0)) • coord 3 + (-(g.E * Real.cos (z 0))) • coord 4)))),
      g.ωc • (g.M⁻¹ • (g.ρ • coord 6 - (2 * g.σ) • ((g.power (z 0) (z 3) (z 4)) • coord 0 +
        (g.E * Real.sin (z 0)) • coord 3 + (-(g.E * Real.cos (z 0))) • coord 4)))]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · exact hasFDerivAt_coord 1 z
    · have h := ((((hasFDerivAt_coord 5 z).sub (hasFDerivAt_coord 2 z)).sub
        ((hasFDerivAt_coord 6 z).mul (hasFDerivAt_coord 1 z))).const_smul g.M⁻¹)
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp; try ring
    · have h := (hP.sub (hasFDerivAt_coord 2 z)).const_smul g.ωc
      convert h using 1
      · funext y; simp
      · ext v; simp; try ring
    · exact g.hasFDerivAt_rateD 0 3 4 z
    · exact g.hasFDerivAt_rateQ 0 3 4 z
    · have h := (((hasFDerivAt_const (g.E ^ 2 * g.X / g.L ^ 2) z).sub
        (hQ.mul_const g.ρ)).const_smul g.M⁻¹).const_smul g.ωc
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp; try ring
    · have h := ((((hasFDerivAt_coord 6 z).mul_const g.ρ).sub
        (hQ.const_mul (2 * g.σ))).const_smul g.M⁻¹).const_smul g.ωc
      convert h using 1
      · funext y; simp [div_eq_inv_mul]
      · ext v; simp; try ring
  · fin_cases i <;> (simp [btJacobian, Fin.sum_univ_seven]; try ring)

/-- **The (BT.3) determinant** at every point:
`det = ω_c³ ρ² (|Z|² P_e − R E²)/(L² M³)`; it vanishes exactly where `P_e = c₀`. -/
@[tmio M, powerlib_domain] theorem det_btJacobian (z : State 7) :
    (g.btJacobian z).det = g.ωc ^ 3 * g.ρ ^ 2 *
      (g.absSq * g.power (z 0) (z 3) (z 4) - g.R * g.E ^ 2) / (g.L ^ 2 * g.M ^ 3) := by
  set c := Real.cos (z 0) with hc
  set s := Real.sin (z 0) with hs
  set P := g.power (z 0) (z 3) (z 4) with hP
  set Q := g.reactive (z 0) (z 3) (z 4) with hQ
  set B : Matrix (Fin 6) (Fin 6) ℝ := !![0, 1, 0, 0, 0, 0;
    -(g.ωc * Q), 0, -g.ωc, g.ωc * (g.E * c), g.ωc * (g.E * s), 0;
    -(g.E * s) / g.L, 0, 0, -g.R / g.L, g.X / g.L, 0;
    g.E * c / g.L, 0, 0, -g.X / g.L, -g.R / g.L, 0;
    -(g.ωc * (g.ρ * P)) / g.M, 0, 0, -(g.ωc * (g.ρ * (g.E * s))) / g.M,
      g.ωc * (g.ρ * (g.E * c)) / g.M, 0;
    -(g.ωc * (2 * g.σ * P)) / g.M, 0, 0, -(g.ωc * (2 * g.σ * (g.E * s))) / g.M,
      g.ωc * (2 * g.σ * (g.E * c)) / g.M, g.ωc * g.ρ / g.M] with hBdef
  set C : Matrix (Fin 5) (Fin 5) ℝ := !![0, 1, 0, 0, 0;
    -(g.ωc * Q), 0, -g.ωc, g.ωc * (g.E * c), g.ωc * (g.E * s);
    -(g.E * s) / g.L, 0, 0, -g.R / g.L, g.X / g.L;
    g.E * c / g.L, 0, 0, -g.X / g.L, -g.R / g.L;
    -(g.ωc * (g.ρ * P)) / g.M, 0, 0, -(g.ωc * (g.ρ * (g.E * s))) / g.M,
      g.ωc * (g.ρ * (g.E * c)) / g.M] with hCdef
  set D : Matrix (Fin 4) (Fin 4) ℝ := !![-(g.ωc * Q), -g.ωc, g.ωc * (g.E * c), g.ωc * (g.E * s);
    -(g.E * s) / g.L, 0, -g.R / g.L, g.X / g.L;
    g.E * c / g.L, 0, -g.X / g.L, -g.R / g.L;
    -(g.ωc * (g.ρ * P)) / g.M, 0, -(g.ωc * (g.ρ * (g.E * s))) / g.M,
      g.ωc * (g.ρ * (g.E * c)) / g.M] with hDdef
  have hB : (g.btJacobian z).submatrix (Fin.succAbove 1) (Fin.succAbove 5) = B := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hC : B.submatrix (Fin.succAbove 5) (Fin.succAbove 5) = C := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hD : C.submatrix Fin.succ (Fin.succAbove 1) = D := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hE : D.submatrix (Fin.succAbove 0) (Fin.succAbove 1) =
      !![-(g.E * s) / g.L, -g.R / g.L, g.X / g.L;
        g.E * c / g.L, -g.X / g.L, -g.R / g.L;
        -(g.ωc * (g.ρ * P)) / g.M, -(g.ωc * (g.ρ * (g.E * s))) / g.M,
          g.ωc * (g.ρ * (g.E * c)) / g.M] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h7 : (g.btJacobian z).det = 1 / g.M * B.det := by
    rw [Matrix.det_succ_column _ 5, Fin.sum_univ_seven, hB]
    simp [btJacobian]
    norm_num
  have h6 : B.det = g.ωc * g.ρ / g.M * C.det := by
    rw [Matrix.det_succ_column _ 5, Fin.sum_univ_six, hC]
    simp [hBdef]
    norm_num
  have h5 : C.det = -D.det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_five, hD]
    simp [hCdef]
  have h4 : D.det = -(g.ωc ^ 2 * (g.ρ / g.M) * (P * (g.R ^ 2 + g.X ^ 2) - g.R * g.E ^ 2) /
      g.L ^ 2) := by
    rw [Matrix.det_succ_column _ 1, Fin.sum_univ_four, hE]
    simp [hDdef, Matrix.det_fin_three]
    linear_combination (g.ωc ^ 2 * g.ρ * g.R * g.E ^ 2 / (g.M * g.L ^ 2)) *
      Real.sin_sq_add_cos_sq (z 0)
  rw [h7, h6, h5, h4, Network.absSq]
  ring

/-- The determinant of the derivative of the (BT.3) map at every point. -/
@[tmio M, powerlib_domain] theorem det_fderiv_btMap (z : State 7) :
    LinearMap.det (fderiv ℝ g.btMap z : State 7 →ₗ[ℝ] State 7) = g.ωc ^ 3 * g.ρ ^ 2 *
      (g.absSq * g.power (z 0) (z 3) (z 4) - g.R * g.E ^ 2) / (g.L ^ 2 * g.M ^ 3) := by
  rw [(g.hasFDerivAt_btMap z).fderiv, Dynamics.det_toEuclideanCLM, g.det_btJacobian z]

/-- The operating point of a model with its parameters, `(δ*, 0, P_ref, i_s(δ*), P_ref, D)`. -/
def Model.btPoint (m : Model) : State 7 :=
  WithLp.toLp 2 ![m.δ, 0, m.g.Pref, (m.g.is m.δ).re, (m.g.is m.δ).im, m.g.Pref, m.g.D]

/-- At a Bogdanov–Takens point (balanced, `K = 0`, `D = D_line`) the (BT.3) map vanishes. -/
@[tmio M, powerlib_domain] theorem Model.btMap_btPoint_eq_zero (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hb : m.g.qssPower m.δ = m.g.Pref) (hK : m.K = 0)
    (hD : m.g.D = m.g.Dline) :
    m.g.btMap m.btPoint = 0 := by
  have hK' : m.g.syncCoeff m.δ = 0 := hK
  have h0 : m.g.ωc * ((m.g.E ^ 2 * m.g.X / m.g.L ^ 2 -
      m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im * m.g.ρ) / m.g.M) = 0 := by
    have h := m.coeff0_eq hL hZ
    rw [Model.K, hK', mul_zero, zero_div, mul_zero] at h
    exact h
  have h1 : m.g.ωc * ((m.g.D * m.g.ρ -
      2 * m.g.σ * m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im) / m.g.M) = 0 := by
    have h := VSM.Model.coeff1_eq ⟨m.g.toVSM, m.δ⟩ hL hZ
    have hK2 : VSM.Model.K ⟨m.g.toVSM, m.δ⟩ = 0 := hK'
    rw [hK2, show m.g.toVSM.D = m.g.Dline from hD, sub_self, mul_zero, mul_zero, add_zero,
      zero_div] at h
    rw [show (m.g.D * m.g.ρ - 2 * m.g.σ * m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im) /
      m.g.M = 0 from h, mul_zero]
  have hr := (m.g.rate_eq_zero_iff hL hZ.ne' m.δ (m.g.is m.δ).re (m.g.is m.δ).im).mpr
    ⟨rfl, rfl⟩
  rw [btMap_apply]
  ext i; fin_cases i
  · show (0 : ℝ) = 0; rfl
  · show (m.g.Pref - m.g.Pref - m.g.D * 0) / m.g.M = 0; simp
  · show m.g.ωc * (m.g.qssPower m.δ - m.g.Pref) = 0; rw [hb, sub_self, mul_zero]
  · exact hr.1
  · exact hr.2
  · exact h0
  · exact h1

/-- **The (BT.3) determinant at the operating point**: `det = ω_c³ ρ³ (P(δ*) − c₀)/M³`. -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_btPoint (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 7 →ₗ[ℝ] State 7) =
      m.g.ωc ^ 3 * m.g.ρ ^ 3 * (m.g.qssPower m.δ - m.g.c0) / m.g.M ^ 3 := by
  rw [det_fderiv_btMap]
  have hP : m.g.power (m.btPoint 0) (m.btPoint 3) (m.btPoint 4) = m.g.qssPower m.δ := rfl
  rw [hP]
  have hρ : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
  have hZ' := hZ.ne'
  rw [Network.c0, hρ]
  field_simp

/-- **Kuznetsov's (BT.3) at a fold of the line with a power filter.** At a fold `K = 0` (in
particular at every Bogdanov–Takens point `K = 0`, `D = D_line`) the (BT.3) determinant is
`± ω_c³ρ³A/M³`; it is nonzero iff `A ≠ 0` (`M, ω_c, L ≠ 0`, `|Z|² > 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_ne_zero_iff (m : Model)
    (hM : m.g.M ≠ 0) (hω : m.g.ωc ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 7 →ₗ[ℝ] State 7) ≠ 0 ↔
      m.g.A ≠ 0 := by
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  have hsq := m.g.sq_qssPower_sub_c0_of_syncCoeff_eq_zero hZ hK
  rw [m.det_fderiv_btMap_btPoint hL hZ, div_ne_zero_iff, mul_ne_zero_iff,
    and_iff_right (mul_ne_zero (pow_ne_zero 3 hω) (pow_ne_zero 3 hρ)),
    and_iff_left (pow_ne_zero 3 hM)]
  constructor
  · intro h hA; apply h; rw [hA] at hsq; simpa using hsq
  · intro hA h; apply hA; rw [h] at hsq; simpa using hsq.symm

/-- **The sign of the (BT.3) determinant** (`M, ω_c > 0`, `L ≠ 0`, `|Z|² > 0`): positive exactly
when the operating power lies above the centre `c₀` of the power-angle curve (the upper fold). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_pos_iff (m : Model) (hM : 0 < m.g.M)
    (hω : 0 < m.g.ωc) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    0 < LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 7 →ₗ[ℝ] State 7) ↔
      m.g.c0 < m.g.qssPower m.δ := by
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (by positivity)
  rw [m.det_fderiv_btMap_btPoint hL hZ, div_pos_iff_of_pos_right (by positivity),
    mul_pos_iff_of_pos_left (by positivity), sub_pos]

/-- **(BT.3) holds at every Bogdanov–Takens point of a physical line with a power filter**: for a
physical network, `M, ω_c ≠ 0`, at a fold `K = 0` — in particular at the Bogdanov–Takens point
`K = 0`, `D = D_line` (`Line.VSMLPF.Model.two_le_rootMultiplicity_zero_iff`) — the derivative of
the (BT.3) map is bijective. -/
@[tmio M, powerlib_domain] theorem Model.bijective_fderiv_btMap (m : Model) (hp : m.g.Physical)
    (hM : m.g.M ≠ 0) (hω : m.g.ωc ≠ 0) (hK : m.K = 0) :
    Function.Bijective (fderiv ℝ m.g.btMap m.btPoint) := by
  have hZ := hp.absSq_pos
  have hA : m.g.A ≠ 0 := div_ne_zero (mul_pos hp.E hp.V).ne' (Real.sqrt_pos.mpr hZ).ne'
  exact Dynamics.bijective_of_det_ne_zero _
    ((m.det_fderiv_btMap_ne_zero_iff hM hω hp.L.ne' hZ hK).mpr hA)

end VSMLPF

/-! ## Power synchronization on the line (three states, parameters `(P_ref, K_p)`) -/

namespace PSC

variable (g : PSC)

/-- The characteristic polynomial of the Jacobian at every state. -/
@[tmio M, powerlib_domain] theorem charpoly_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).charpoly = X ^ 3 + C (g.coeff2 (g.reactive δ id iq)) * X ^ 2 +
      C (g.coeff1 (g.reactive δ id iq)) * X + C (g.coeff0 (g.reactive δ id iq)) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  apply Polynomial.funext
  intro s
  rw [← Matrix.charpoly_map, ← Linear.det_characteristicMatrix_eq_eval,
    g.det_characteristicMatrix]
  simp

/-- The set-point and the gain replaced: the unfolding parameters `(P_ref, K_p)`. -/
def withParams (P K : ℝ) : PSC := { g with Pref := P, Kp := K }

/-- The state `(δ, i_d, i_q)` of a point `(δ, i_d, i_q, P_ref, K_p)`. -/
def btState (z : State 5) : State 3 := WithLp.toLp 2 ![z 0, z 1, z 2]

/-- **Kuznetsov's (BT.3) map** of the unfolding in `(P_ref, K_p)`:
`(δ, i_d, i_q, P_ref, K_p) ↦ (f(x; P_ref, K_p), a₀, a₁)`, `a₀, a₁` the two lowest coefficients
of the characteristic polynomial of the (`fderiv`) Jacobian `PSC.jacobian`. -/
def btMap (z : State 5) : State 5 :=
  WithLp.toLp 2 ![(g.withParams (z 3) (z 4)).field (btState z) 0,
    (g.withParams (z 3) (z 4)).field (btState z) 1,
    (g.withParams (z 3) (z 4)).field (btState z) 2,
    ((g.withParams (z 3) (z 4)).jacobian (z 0) (z 1) (z 2)).charpoly.coeff 0,
    ((g.withParams (z 3) (z 4)).jacobian (z 0) (z 1) (z 2)).charpoly.coeff 1]

/-- The (BT.3) map in closed form. -/
@[tmio M, powerlib_domain] theorem btMap_apply (z : State 5) :
    g.btMap z = WithLp.toLp 2 ![z 4 * (z 3 - g.power (z 0) (z 1) (z 2)),
      g.rateD (z 0) (z 1) (z 2), g.rateQ (z 0) (z 1) (z 2),
      z 4 * (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (z 0) (z 1) (z 2) * g.ρ),
      g.ρ - 2 * g.σ * (z 4 * g.reactive (z 0) (z 1) (z 2))] := by
  simp only [btMap, charpoly_jacobian]
  simp [coeff_X, coeff_C, withParams, field, btState, coeff0, coeff1]

/-- The Jacobian matrix of the (BT.3) map. -/
def btJacobian (z : State 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![z 4 * g.reactive (z 0) (z 1) (z 2), -(z 4 * (g.E * Real.cos (z 0))),
      -(z 4 * (g.E * Real.sin (z 0))), z 4, z 3 - g.power (z 0) (z 1) (z 2);
    -(g.E * Real.sin (z 0)) / g.L, -g.R / g.L, g.X / g.L, 0, 0;
    g.E * Real.cos (z 0) / g.L, -g.X / g.L, -g.R / g.L, 0, 0;
    -(z 4 * (g.ρ * g.power (z 0) (z 1) (z 2))), -(z 4 * (g.ρ * (g.E * Real.sin (z 0)))),
      z 4 * (g.ρ * (g.E * Real.cos (z 0))), 0,
      g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (z 0) (z 1) (z 2) * g.ρ;
    -(2 * g.σ * (z 4 * g.power (z 0) (z 1) (z 2))),
      -(2 * g.σ * (z 4 * (g.E * Real.sin (z 0)))), 2 * g.σ * (z 4 * (g.E * Real.cos (z 0))),
      0, -(2 * g.σ * g.reactive (z 0) (z 1) (z 2))]

@[tmio M, powerlib_domain] theorem hasFDerivAt_btMap (z : State 5) :
    HasFDerivAt g.btMap (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.btJacobian z)) z := by
  have hf : g.btMap = fun y : State 5 => WithLp.toLp 2 ![y 4 * (y 3 - g.power (y 0) (y 1) (y 2)),
      g.rateD (y 0) (y 1) (y 2), g.rateQ (y 0) (y 1) (y 2),
      y 4 * (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (y 0) (y 1) (y 2) * g.ρ),
      g.ρ - 2 * g.σ * (y 4 * g.reactive (y 0) (y 1) (y 2))] := funext g.btMap_apply
  have hP := g.hasFDerivAt_power 0 1 2 z
  have hQ := g.hasFDerivAt_reactive 0 1 2 z
  rw [hf]
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![z 4 • (coord 3 - ((-g.reactive (z 0) (z 1) (z 2)) • coord 0 +
        (g.E * Real.cos (z 0)) • coord 1 + (g.E * Real.sin (z 0)) • coord 2)) +
        (z 3 - g.power (z 0) (z 1) (z 2)) • coord 4,
      (-(g.E * Real.sin (z 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 1 + (g.X / g.L) • coord 2,
      (g.E * Real.cos (z 0) / g.L) • coord 0 + (-g.X / g.L) • coord 1 + (-g.R / g.L) • coord 2,
      z 4 • (-(g.ρ • ((g.power (z 0) (z 1) (z 2)) • coord 0 +
        (g.E * Real.sin (z 0)) • coord 1 + (-(g.E * Real.cos (z 0))) • coord 2))) +
        (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive (z 0) (z 1) (z 2) * g.ρ) • coord 4,
      -((2 * g.σ) • (z 4 • ((g.power (z 0) (z 1) (z 2)) • coord 0 +
        (g.E * Real.sin (z 0)) • coord 1 + (-(g.E * Real.cos (z 0))) • coord 2) +
        g.reactive (z 0) (z 1) (z 2) • coord 4))]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · have h := (hasFDerivAt_coord 4 z).mul ((hasFDerivAt_coord 3 z).sub hP)
      convert h using 1
      all_goals (ext v; simp; try ring)
    · exact g.hasFDerivAt_rateD 0 1 2 z
    · exact g.hasFDerivAt_rateQ 0 1 2 z
    · have h := (hasFDerivAt_coord 4 z).mul
        ((hasFDerivAt_const (g.E ^ 2 * g.X / g.L ^ 2) z).sub (hQ.mul_const g.ρ))
      convert h using 1
      all_goals (ext v; simp; try ring)
    · have h := (hasFDerivAt_const g.ρ z).sub
        (((hasFDerivAt_coord 4 z).mul hQ).const_mul (2 * g.σ))
      convert h using 1
      all_goals (ext v; simp; try ring)
  · fin_cases i <;> (simp [btJacobian, Fin.sum_univ_five]; try ring)

/-- **The (BT.3) determinant** at every point:
`det = 2 E² K_p² R X (R E² − |Z|² P_e)/L⁵`; it vanishes exactly where `P_e = c₀` (or on a
lossless line, where the line has no Bogdanov–Takens point). -/
@[tmio M, powerlib_domain] theorem det_btJacobian (z : State 5) :
    (g.btJacobian z).det = 2 * g.E ^ 2 * z 4 ^ 2 * g.R * g.X *
      (g.R * g.E ^ 2 - g.absSq * g.power (z 0) (z 1) (z 2)) / g.L ^ 5 := by
  set c := Real.cos (z 0) with hc
  set s := Real.sin (z 0) with hs
  set P := g.power (z 0) (z 1) (z 2) with hP
  set Q := g.reactive (z 0) (z 1) (z 2) with hQ
  set k := z 4 with hk
  set B : Matrix (Fin 4) (Fin 4) ℝ := !![-(g.E * s) / g.L, -g.R / g.L, g.X / g.L, 0;
    g.E * c / g.L, -g.X / g.L, -g.R / g.L, 0;
    -(k * (g.ρ * P)), -(k * (g.ρ * (g.E * s))), k * (g.ρ * (g.E * c)),
      g.E ^ 2 * g.X / g.L ^ 2 - Q * g.ρ;
    -(2 * g.σ * (k * P)), -(2 * g.σ * (k * (g.E * s))), 2 * g.σ * (k * (g.E * c)),
      -(2 * g.σ * Q)] with hBdef
  have hB : (g.btJacobian z).submatrix (Fin.succAbove 0) (Fin.succAbove 3) = B := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hB2 : B.submatrix (Fin.succAbove 2) (Fin.succAbove 3) =
      !![-(g.E * s) / g.L, -g.R / g.L, g.X / g.L;
        g.E * c / g.L, -g.X / g.L, -g.R / g.L;
        -(2 * g.σ * (k * P)), -(2 * g.σ * (k * (g.E * s))), 2 * g.σ * (k * (g.E * c))] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hB3 : B.submatrix (Fin.succAbove 3) (Fin.succAbove 3) =
      !![-(g.E * s) / g.L, -g.R / g.L, g.X / g.L;
        g.E * c / g.L, -g.X / g.L, -g.R / g.L;
        -(k * (g.ρ * P)), -(k * (g.ρ * (g.E * s))), k * (g.ρ * (g.E * c))] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h5 : (g.btJacobian z).det = -(k * B.det) := by
    rw [Matrix.det_succ_column _ 3, Fin.sum_univ_five, hB]
    simp [btJacobian]
    rw [hk]; ring
  have h4 : B.det = -(2 * g.σ * k * (g.E ^ 2 * g.X / g.L ^ 2) *
      ((g.R * g.E ^ 2 - (g.R ^ 2 + g.X ^ 2) * P) / g.L ^ 2)) := by
    rw [Matrix.det_succ_column _ 3, Fin.sum_univ_four, hB2, hB3]
    simp [hBdef, Matrix.det_fin_three]
    linear_combination (-(2 * g.E ^ 4 * g.R * g.X * k * g.σ) / g.L ^ 4) *
      Real.sin_sq_add_cos_sq (z 0)
  rw [h5, h4, Network.absSq, Network.σ]
  field_simp

/-- The determinant of the derivative of the (BT.3) map at every point. -/
@[tmio M, powerlib_domain] theorem det_fderiv_btMap (z : State 5) :
    LinearMap.det (fderiv ℝ g.btMap z : State 5 →ₗ[ℝ] State 5) = 2 * g.E ^ 2 * z 4 ^ 2 * g.R *
      g.X * (g.R * g.E ^ 2 - g.absSq * g.power (z 0) (z 1) (z 2)) / g.L ^ 5 := by
  rw [(g.hasFDerivAt_btMap z).fderiv, Dynamics.det_toEuclideanCLM, g.det_btJacobian z]

/-- The operating point of a model with its parameters, `(δ*, i_s(δ*), P_ref, K_p)`. -/
def Model.btPoint (m : Model) : State 5 :=
  WithLp.toLp 2 ![m.δ, (m.g.is m.δ).re, (m.g.is m.δ).im, m.g.Pref, m.g.Kp]

/-- **The (BT.3) determinant at the operating point**:
`det = −2 E² K_p² R X |Z|² (P(δ*) − c₀)/L⁵`. -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_btPoint (m : Model)
    (hZ : 0 < m.g.absSq) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 5 →ₗ[ℝ] State 5) =
      -(2 * m.g.E ^ 2 * m.g.Kp ^ 2 * m.g.R * m.g.X * m.g.absSq *
        (m.g.qssPower m.δ - m.g.c0) / m.g.L ^ 5) := by
  rw [det_fderiv_btMap]
  have hP : m.g.power (m.btPoint 0) (m.btPoint 1) (m.btPoint 2) = m.g.qssPower m.δ := rfl
  have hk : m.btPoint 4 = m.g.Kp := rfl
  rw [hP, hk, Network.c0]
  have hZ' := hZ.ne'
  field_simp
  ring

/-- At a Bogdanov–Takens gain `K_p D_line = 1` the network is lossy and reactive:
`E, R, X, L ≠ 0` (`D_line = 2E²RXL/|Z|⁴`) and `K_p ≠ 0`. -/
@[tmio M, powerlib_domain] private theorem ne_zero_of_bt (m : Model)
    (hbt : m.g.Kp * m.g.Dline = 1) :
    m.g.Kp ≠ 0 ∧ m.g.E ≠ 0 ∧ m.g.R ≠ 0 ∧ m.g.X ≠ 0 ∧ m.g.L ≠ 0 := by
  have hD : m.g.Dline ≠ 0 := right_ne_zero_of_mul (by rw [hbt]; exact one_ne_zero)
  have hK : m.g.Kp ≠ 0 := left_ne_zero_of_mul (by rw [hbt]; exact one_ne_zero)
  simp only [Network.Dline, ne_eq, div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or, not_or] at hD
  exact ⟨hK, fun h => hD.1.1.1.1 (by rw [h]; ring), hD.1.1.1.2, hD.1.1.2, hD.1.2⟩

/-- At a Bogdanov–Takens point (balanced, `K = 0`, `K_p D_line = 1`) the (BT.3) map vanishes. -/
@[tmio M, powerlib_domain] theorem Model.btMap_btPoint_eq_zero (m : Model) (hZ : 0 < m.g.absSq)
    (hb : m.g.qssPower m.δ = m.g.Pref) (hK : m.K = 0) (hbt : m.g.Kp * m.g.Dline = 1) :
    m.g.btMap m.btPoint = 0 := by
  obtain ⟨hKp, -, -, -, hL⟩ := ne_zero_of_bt m hbt
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  have hK' : m.g.syncCoeff m.δ = 0 := hK
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.κ := by
    have h := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [hK', zero_add] at h; exact h
  have h0 : m.g.Kp * (m.g.E ^ 2 * m.g.X / m.g.L ^ 2 -
      m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im * m.g.ρ) = 0 := by
    have h := m.coeff0_eq hL hZ
    rw [Model.K, hK', mul_zero, mul_zero] at h
    exact h
  have h1 : m.g.ρ - 2 * m.g.σ * (m.g.Kp *
      m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im) = 0 := by
    have hD := m.g.Dline_eq hL hZ.ne'
    rw [hQ]
    have : 2 * m.g.σ * m.g.κ = m.g.ρ * m.g.Dline := by rw [hD]; field_simp
    linear_combination (-m.g.Kp) * this - m.g.ρ * hbt
  have hr := (m.g.rate_eq_zero_iff hL hZ.ne' m.δ (m.g.is m.δ).re (m.g.is m.δ).im).mpr
    ⟨rfl, rfl⟩
  rw [btMap_apply]
  ext i; fin_cases i
  · show m.g.Kp * (m.g.Pref - m.g.qssPower m.δ) = 0; rw [hb, sub_self, mul_zero]
  · exact hr.1
  · exact hr.2
  · exact h0
  · exact h1

/-- **Kuznetsov's (BT.3) at the Bogdanov–Takens point of power synchronization.** At `K = 0`
with the Bogdanov–Takens gain `K_p D_line = 1` the (BT.3) determinant is
`∓ K_p ρ³ A`; it is nonzero iff `A ≠ 0` (`|Z|² > 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_ne_zero_iff (m : Model)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) (hbt : m.g.Kp * m.g.Dline = 1) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 5 →ₗ[ℝ] State 5) ≠ 0 ↔
      m.g.A ≠ 0 := by
  obtain ⟨hKp, hE, hR, hX, hL⟩ := ne_zero_of_bt m hbt
  have hsq := m.g.sq_qssPower_sub_c0_of_syncCoeff_eq_zero hZ hK
  have hc : 2 * m.g.E ^ 2 * m.g.Kp ^ 2 * m.g.R * m.g.X * m.g.absSq ≠ 0 := by
    have := hZ.ne'; positivity
  rw [m.det_fderiv_btMap_btPoint hZ, neg_ne_zero, div_ne_zero_iff, mul_ne_zero_iff,
    and_iff_right hc, and_iff_left (pow_ne_zero 5 hL)]
  constructor
  · intro h hA; apply h; rw [hA] at hsq; simpa using hsq
  · intro hA h; apply hA; rw [h] at hsq; simpa using hsq.symm

/-- **The sign of the (BT.3) determinant** on a lossy reactive line (`R, X, L > 0`, `E, K_p ≠ 0`):
negative exactly when the operating power lies above the centre `c₀` (the upper fold). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_neg_iff (m : Model) (hE : m.g.E ≠ 0)
    (hKp : m.g.Kp ≠ 0) (hR : 0 < m.g.R) (hX : 0 < m.g.X) (hL : 0 < m.g.L) :
    LinearMap.det (fderiv ℝ m.g.btMap m.btPoint : State 5 →ₗ[ℝ] State 5) < 0 ↔
      m.g.c0 < m.g.qssPower m.δ := by
  have hZ : 0 < m.g.absSq := by unfold Network.absSq; positivity
  have hc : 0 < 2 * m.g.E ^ 2 * m.g.Kp ^ 2 * m.g.R * m.g.X * m.g.absSq := by positivity
  rw [m.det_fderiv_btMap_btPoint hZ, neg_lt_zero, div_pos_iff_of_pos_right (by positivity),
    mul_pos_iff_of_pos_left hc, sub_pos]

/-- **(BT.3) holds at every Bogdanov–Takens point of power synchronization with `A ≠ 0`**: at
`K = 0` and `K_p D_line = 1` (`|Z|² > 0`) the derivative of the (BT.3) map is bijective;
for a physical network `A = E V/|Z| > 0`. -/
@[tmio M, powerlib_domain] theorem Model.bijective_fderiv_btMap (m : Model) (hZ : 0 < m.g.absSq)
    (hA : m.g.A ≠ 0) (hK : m.K = 0) (hbt : m.g.Kp * m.g.Dline = 1) :
    Function.Bijective (fderiv ℝ m.g.btMap m.btPoint) :=
  Dynamics.bijective_of_det_ne_zero _ ((m.det_fderiv_btMap_ne_zero_iff hZ hK hbt).mpr hA)

end PSC

end powerlib.GFM.Line

/-! ## The quasi-static VSM with a power filter (three states, parameters `(P_ref, D)`) -/

namespace powerlib.GFM.VSMLPFLossy
open Polynomial Matrix
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components
  mk3)

variable (p : VSMLPFLossy)

/-- The set-point and the damping replaced: the unfolding parameters `(P_ref, D)`. -/
def withParams (P D : ℝ) : VSMLPFLossy := { p with Pref := P, D := D }

/-- The state `(δ, ω, P_f)` of a point `(δ, ω, P_f, P_ref, D)`. -/
def btState (z : State 5) : State 3 := mk3 (z 0) (z 1) (z 2)

/-- **Kuznetsov's (BT.3) map** of the unfolding in `(P_ref, D)`:
`(δ, ω, P_f, P_ref, D) ↦ (f(x; P_ref, D), a₀, a₁)`, `a₀, a₁` the two lowest coefficients of the
characteristic polynomial of the Jacobian `VSMLPF.jacobian (δ − α)` of the lossy field
(`VSMLPFLossy.hasFDerivAt_field`). -/
def btMap (z : State 5) : State 5 :=
  WithLp.toLp 2 ![(p.withParams (z 3) (z 4)).field (btState z) 0,
    (p.withParams (z 3) (z 4)).field (btState z) 1,
    (p.withParams (z 3) (z 4)).field (btState z) 2,
    ((p.withParams (z 3) (z 4)).toVSMLPF.jacobian (z 0 - p.α)).charpoly.coeff 0,
    ((p.withParams (z 3) (z 4)).toVSMLPF.jacobian (z 0 - p.α)).charpoly.coeff 1]

/-- The (BT.3) map in closed form. -/
@[tmio M, powerlib_domain] theorem btMap_apply (z : State 5) :
    p.btMap z = WithLp.toLp 2 ![z 1, (z 3 - z 2 - z 4 * z 1) / p.M,
      p.ωc * (p.c0 + p.A * Real.sin (z 0 - p.α) - z 2),
      p.ωc * (p.A * Real.cos (z 0 - p.α)) / p.M, z 4 * p.ωc / p.M] := by
  simp only [btMap, VSMLPF.charpoly_jacobian]
  simp [withParams, field, btState, toVSMLPF, Pe, coeff_mul_X_pow', coeff_X, coeff_C]

/-- The Jacobian matrix of the (BT.3) map. -/
def btJacobian (z : State 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 0;
    0, -z 4 / p.M, -1 / p.M, 1 / p.M, -z 1 / p.M;
    p.ωc * (p.A * Real.cos (z 0 - p.α)), 0, -p.ωc, 0, 0;
    -(p.ωc * (p.A * Real.sin (z 0 - p.α))) / p.M, 0, 0, 0, 0;
    0, 0, 0, 0, p.ωc / p.M]

@[tmio M, powerlib_domain] theorem hasFDerivAt_btMap (z : State 5) :
    HasFDerivAt p.btMap (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (p.btJacobian z)) z := by
  have hf : p.btMap = fun y : State 5 => WithLp.toLp 2 ![y 1, (y 3 - y 2 - y 4 * y 1) / p.M,
      p.ωc * (p.c0 + p.A * Real.sin (y 0 - p.α) - y 2),
      p.ωc * (p.A * Real.cos (y 0 - p.α)) / p.M, y 4 * p.ωc / p.M] := funext p.btMap_apply
  have h0 := (hasFDerivAt_coord 0 z).sub_const p.α
  have hsin := (Real.hasDerivAt_sin (z 0 - p.α)).comp_hasFDerivAt z h0
  have hcos := (Real.hasDerivAt_cos (z 0 - p.α)).comp_hasFDerivAt z h0
  rw [hf]
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![coord 1, p.M⁻¹ • (coord 3 - coord 2 - (z 4 • coord 1 + z 1 • coord 4)),
      p.ωc • ((p.A * Real.cos (z 0 - p.α)) • coord 0 - coord 2),
      (p.ωc * (p.A * -Real.sin (z 0 - p.α)) / p.M) • coord 0, (p.ωc / p.M) • coord 4]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · exact hasFDerivAt_coord 1 z
    · have h := ((((hasFDerivAt_coord 3 z).sub (hasFDerivAt_coord 2 z)).sub
        ((hasFDerivAt_coord 4 z).mul (hasFDerivAt_coord 1 z))).const_smul p.M⁻¹)
      convert h using 1
      all_goals (ext v; simp [div_eq_inv_mul]; try ring)
    · have h := (((hsin.const_mul p.A).const_add p.c0).sub (hasFDerivAt_coord 2 z)).const_mul p.ωc
      convert h using 1
      all_goals (ext v; simp [mul_assoc]; try ring)
    · have h := ((hcos.const_mul p.A).const_mul p.ωc).mul_const p.M⁻¹
      convert h using 1
      all_goals (ext v; simp [div_eq_mul_inv]; try ring)
    · have h := ((hasFDerivAt_coord 4 z).mul_const p.ωc).mul_const p.M⁻¹
      convert h using 1
      all_goals (ext v; simp [div_eq_mul_inv]; try ring)
  · fin_cases i <;> (simp [btJacobian, Fin.sum_univ_five]; try ring)

/-- **The (BT.3) determinant** at every point: `det = ω_c³ A sin(δ − α)/M³ = ω_c³ (P(δ) − c₀)/M³`;
it vanishes exactly where `P(δ) = c₀`. -/
@[tmio M, powerlib_domain] theorem det_btJacobian (z : State 5) :
    (p.btJacobian z).det = p.ωc ^ 3 * (p.Pe (z 0) - p.c0) / p.M ^ 3 := by
  set c := Real.cos (z 0 - p.α) with hc
  set s := Real.sin (z 0 - p.α) with hs
  set B : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0;
    0, -z 4 / p.M, -1 / p.M, 1 / p.M;
    p.ωc * (p.A * c), 0, -p.ωc, 0;
    -(p.ωc * (p.A * s)) / p.M, 0, 0, 0] with hBdef
  have hB : (p.btJacobian z).submatrix (Fin.succAbove 4) (Fin.succAbove 4) = B := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hC : B.submatrix Fin.succ (Fin.succAbove 1) =
      !![0, -1 / p.M, 1 / p.M;
        p.ωc * (p.A * c), -p.ωc, 0;
        -(p.ωc * (p.A * s)) / p.M, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h5 : (p.btJacobian z).det = p.ωc / p.M * B.det := by
    rw [Matrix.det_succ_row _ 4, Fin.sum_univ_five, hB]
    simp [btJacobian]
    norm_num
  have h4 : B.det = p.ωc ^ 2 * (p.A * s) / p.M ^ 2 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, hC]
    simp [hBdef, Matrix.det_fin_three]
    ring
  rw [h5, h4, Pe, hs]
  ring

/-- The determinant of the derivative of the (BT.3) map at every point. -/
@[tmio M, powerlib_domain] theorem det_fderiv_btMap (z : State 5) :
    LinearMap.det (fderiv ℝ p.btMap z : State 5 →ₗ[ℝ] State 5) =
      p.ωc ^ 3 * (p.Pe (z 0) - p.c0) / p.M ^ 3 := by
  rw [(p.hasFDerivAt_btMap z).fderiv, Dynamics.det_toEuclideanCLM, p.det_btJacobian z]

/-- The operating point of a model with its parameters, `(δ*, 0, P_ref, P_ref, D)`. -/
def Model.btPoint (m : Model) : State 5 := WithLp.toLp 2 ![m.δ, 0, m.p.Pref, m.p.Pref, m.p.D]

/-- At the Bogdanov–Takens corner (`D = 0`, `K = 0`, power balance) the (BT.3) map vanishes. -/
@[tmio M, powerlib_domain] theorem Model.btMap_btPoint_eq_zero (m : Model) (hD : m.p.D = 0)
    (hK : m.K = 0) (hb : m.p.Pe m.δ = m.p.Pref) : m.p.btMap m.btPoint = 0 := by
  have hK' : m.p.A * Real.cos (m.δ - m.p.α) = 0 := hK
  rw [btMap_apply]
  ext i; fin_cases i
  · show (0 : ℝ) = 0; rfl
  · show (m.p.Pref - m.p.Pref - m.p.D * 0) / m.p.M = 0; simp
  · show m.p.ωc * (m.p.c0 + m.p.A * Real.sin (m.δ - m.p.α) - m.p.Pref) = 0
    rw [← hb, Pe, sub_self, mul_zero]
  · show m.p.ωc * (m.p.A * Real.cos (m.δ - m.p.α)) / m.p.M = 0
    rw [hK', mul_zero, zero_div]
  · show m.p.D * m.p.ωc / m.p.M = 0
    rw [hD, zero_mul, zero_div]

/-- **The (BT.3) determinant at the operating point**: `det = ω_c³ (P(δ*) − c₀)/M³`. -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_btPoint (m : Model) :
    LinearMap.det (fderiv ℝ m.p.btMap m.btPoint : State 5 →ₗ[ℝ] State 5) =
      m.p.ωc ^ 3 * (m.p.Pe m.δ - m.p.c0) / m.p.M ^ 3 :=
  m.p.det_fderiv_btMap m.btPoint

/-- **Kuznetsov's (BT.3) at a fold of the quasi-static model.** At a fold `K = 0` (in particular
at the Bogdanov–Takens corner `D = 0`, `VSMLPF.two_le_rootMultiplicity_zero_iff`) the (BT.3)
determinant is `± ω_c³A/M³`; it is nonzero iff `A ≠ 0` (`M, ω_c ≠ 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_ne_zero_iff (m : Model)
    (hM : m.p.M ≠ 0) (hω : m.p.ωc ≠ 0) (hK : m.K = 0) :
    LinearMap.det (fderiv ℝ m.p.btMap m.btPoint : State 5 →ₗ[ℝ] State 5) ≠ 0 ↔
      m.p.A ≠ 0 := by
  have hsq : (m.p.Pe m.δ - m.p.c0) ^ 2 = m.p.A ^ 2 := by
    have hc := Real.sin_sq_add_cos_sq (m.δ - m.p.α)
    have hK' : m.p.A * Real.cos (m.δ - m.p.α) = 0 := hK
    simp only [Pe, add_sub_cancel_left]
    linear_combination m.p.A ^ 2 * hc - m.p.A * Real.cos (m.δ - m.p.α) * hK'
  rw [m.det_fderiv_btMap_btPoint, div_ne_zero_iff, mul_ne_zero_iff,
    and_iff_right (pow_ne_zero 3 hω), and_iff_left (pow_ne_zero 3 hM)]
  constructor
  · intro h hA; apply h; rw [hA] at hsq; simpa using hsq
  · intro hA h; apply hA; rw [h] at hsq; simpa using hsq.symm

/-- **The sign of the (BT.3) determinant** (`M, ω_c > 0`): positive exactly when the operating
power lies above the centre `c₀` of the power-angle curve (the upper fold). -/
@[tmio M, powerlib_domain] theorem Model.det_fderiv_btMap_pos_iff (m : Model) (hM : 0 < m.p.M)
    (hω : 0 < m.p.ωc) :
    0 < LinearMap.det (fderiv ℝ m.p.btMap m.btPoint : State 5 →ₗ[ℝ] State 5) ↔
      m.p.c0 < m.p.Pe m.δ := by
  rw [m.det_fderiv_btMap_btPoint, div_pos_iff_of_pos_right (by positivity),
    mul_pos_iff_of_pos_left (by positivity), sub_pos]

/-- **(BT.3) holds at the Bogdanov–Takens corner**: for `M, ω_c ≠ 0` and `A ≠ 0`, at a fold
`K = 0` (the corner has also `D = 0`) the derivative of the (BT.3) map is bijective. -/
@[tmio M, powerlib_domain] theorem Model.bijective_fderiv_btMap (m : Model) (hM : m.p.M ≠ 0)
    (hω : m.p.ωc ≠ 0) (hA : m.p.A ≠ 0) (hK : m.K = 0) :
    Function.Bijective (fderiv ℝ m.p.btMap m.btPoint) :=
  Dynamics.bijective_of_det_ne_zero _ ((m.det_fderiv_btMap_ne_zero_iff hM hω hK).mpr hA)

end powerlib.GFM.VSMLPFLossy
