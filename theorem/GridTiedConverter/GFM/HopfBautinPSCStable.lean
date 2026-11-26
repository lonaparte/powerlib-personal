import theorem.GridTiedConverter.GFM.HopfBautinPSCAngle

/-! # A locally asymptotically stable Bautin point of power synchronization on an R–L line

Domain module.

Model boundary.
* The three-state power-synchronization law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged (state `(δ, i_d, i_q)`, grid dq
  frame, export-positive power, `δ̇ = K_p (P_ref − P_e)`, `L i̇ = E e^{jδ} − V − (R + jX) i`), read
  about a selected angle (`Line.PSC.Model`) on `Line.PSC.family`. Excluded as there.
* The point `BautinStable.bpt`: `E = R = L = 1`, `ω₀ = 5`, `V = 5√2/4`, `K_p = 52/5`,
  `P_ref = −1/4`, `δ* = −π/4`; there `Q = 0` (`κ = 0`), `a₂ = 2`, `a₁ = 26`, `a₀ = 52`
  (`det(sI − J) = (s² + 26)(s + 2)`), the angle term `t = −13` and
  `𝔅_P(0, 1, 5, −13) = 𝔊_P · 845 + a₂ a₁² ℌ_P = −3515200 + 3515200 = 0`.
* The rotated frame of `theorem/GridTiedConverter/GFM/HopfBautinPSCAngle.lean`
  (`Line.PSC.Model.field_rotT`): with `z = R_{π/4} x` the translated field is
  `J_rot z + f_rot(z)`, `J_rot = [[0, −52/5, 0], [0, −1, 5], [1, −5, −1]]`,
  `f_rot = ((13/5)(cos z₀ − 1) − (52/5)((cos z₀ − 1) z₁ + sin z₀ z₂), cos z₀ − 1, sin z₀ − z₀)`.
* The chart: the rational chart `ι' y = y₀ a + y₁ b` of the rotated frame, `a = Re q = (0, 5, 1)`,
  `b = Im q/√26 = (2, 0, 1)` (`q = (2√26 i, 5, 1 + √26 i)`), its left inverse `π'` vanishing on the
  stable eigenvector `w = (26/5, 1, −1/5)` (`J_rot w = −2 w`), the reduced linear part
  `rotR y = (y₁, −26 y₀)`; in the grid frame `ι = R_{−π/4} ι'`, `π = π' R_{π/4}`, a chart of the
  critical plane of `(R_{−π/4} q, R_{−π/4} p)` at `ω = √26`. The approximate centre manifold is
  `φ = R_{−π/4} H ∘ π`, `H(y) = h(y) w`, `h` of degrees two to four with rational coefficients.
* Level: exact. The trigonometric nonlinearities enter through the sixth-order Taylor remainders
  of `cos` and `sin`; the rotation is exact; the homological identities and every chart identity
  are rational; `l₁ = 0` and `l₂ = −1525502329√26/8032500` are computed in `ℚ(√26)`. No floating
  point, sampling or search.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3 (Bautin points, the
second Lyapunov coefficient, the sign of `l₂` separating sub- and supercritical Bautin points);
Carr, *Applications of Centre Manifold Theory* (1981), §2.4–2.5. The family law is
`Line.PSC.mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`
(`theorem/GridTiedConverter/GFM/HopfBautinPSC.lean`, generic law
`Dynamics.CenterManifold.localAsymptoticStable_of_dichotomy_reduced_l2_neg`); the critical pair is
`Line.PSC.Model.isCriticalPair_crit`, the degeneracy `Line.PSC.Model.sign_firstLyapunov_crit`
(`theorem/GridTiedConverter/GFM/HopfLinePSC.lean`). The point was found by an exact search for
rational Bautin points with `σ = 1` (on an angle path the Bautin points are
`t = a₁ (1 ± √(−((κ − σ)² + ω₀²) 𝔆_P/𝔊_P))`, `Line.PSC.bautinForm_eq_cubic`; here `𝔊_P = −4160`,
`𝔆_P = 360`, `t = −13`); the centre manifold, the jet and the Lyapunov chain were derived with
SymPy in exact rational and `ℚ(√26)` arithmetic (untrusted, discovery evidence only); every
identity is checked here.

Results.
* The point: `BautinStable.bpt`, `BautinStable.bpt_trig`, `BautinStable.bpt_physical`,
  `BautinStable.bpt_balanced`, `BautinStable.bpt_Q` (`Q = 0`), `BautinStable.bpt_coeffs`,
  `BautinStable.bpt_angleShift` (`t = −13`), **`BautinStable.bpt_firstLyapunov`** (a critical pair
  at `ω = √26` exists and every critical pair has `ℓ₁ = 0`).
* The rotated field: `BautinStable.rotJ_apply`, `BautinStable.fderiv_rotT`, `BautinStable.frot`,
  `BautinStable.frot_apply`, `BautinStable.fnl`, `BautinStable.fnl_rotT`; the critical pair
  `BautinStable.r`, `BautinStable.r_pos`, `BautinStable.r_sq`, `BautinStable.qv`,
  `BautinStable.pv3`, `BautinStable.critQ_eq`, `BautinStable.critP_eq`,
  `BautinStable.isCriticalPair_bpt`.
* The charts: `BautinStable.iotaR`, `BautinStable.piR`, `BautinStable.rotR`, `BautinStable.wv`,
  `BautinStable.iotaR_apply`, `BautinStable.piR_apply`, `BautinStable.rotR_apply`,
  `BautinStable.rotR_rotR`, `BautinStable.piR_iotaR`, `BautinStable.piR_wv`, `BautinStable.A_wv`,
  `BautinStable.piR_A_iotaR`, `BautinStable.isChart_R`, `BautinStable.sub_iotaR_piR`;
  `BautinStable.iotaG`, `BautinStable.piG`, `BautinStable.piG_rotT`, **`BautinStable.isChart_G`**,
  `BautinStable.sub_iotaG_piG`.
* The manifold: `BautinStable.hL2` … `BautinStable.hL4`, `BautinStable.hL`,
  `BautinStable.manifoldH`, `BautinStable.manifoldG`, `BautinStable.manifold` and the hypotheses
  on `φ` (`BautinStable.contDiffAt_manifold`, `BautinStable.manifold_zero`,
  `BautinStable.fderiv_manifold_zero`, `BautinStable.critP_manifold`).
* The chart field and its quintic jet: `BautinStable.chartPt`, `BautinStable.chartField_eq`,
  `BautinStable.lin0` … `BautinStable.lin2`, `BautinStable.chartPt_apply`, `BautinStable.G_eq`,
  `BautinStable.low1_eq` … `BautinStable.low3_eq`, `BautinStable.split1_isBigO` …
  `BautinStable.split3_isBigO`, `BautinStable.f1_sub_low` … `BautinStable.f3_sub_low`,
  `BautinStable.cF_eq`, `BautinStable.cG_eq`, `BautinStable.G0_sub_jet`,
  `BautinStable.G1_sub_jet`, `BautinStable.jet_tail_bounds`.
* **The invariance defect is `O(‖u‖⁵)`**: `BautinStable.dcomp`, `BautinStable.main_eq_high`,
  `BautinStable.defect_eq`, `BautinStable.dcomp_isBigO`, `BautinStable.isOrder_defect`.
* The jet in the rotation frame: `BautinStable.jet`, `BautinStable.jetN`,
  `BautinStable.frameY_rotR`, `BautinStable.jetF_frame`, `BautinStable.jetG_frame`,
  `BautinStable.jet_nrm`; the Lyapunov chain `BautinStable.jv_c30` … `BautinStable.jv_l2`;
  **`BautinStable.jet_l1_eq_zero`** and **`BautinStable.jet_l2_eq`**
  (`l₂(J) = −1525502329√26/8032500 < 0`).

Family and connection conclusions.
No new family: connection conclusions on `Line.PSC.family`.
* **`Line.PSC.stable_bautin_mem_den_locallyAsymptoticallyStable`**: the Bautin point
  `BautinStable.bpt` is locally asymptotically stable (a weak focus of the second order with
  `l₂ < 0`, a supercritical Bautin point). With the unstable Bautin points
  `Line.PSC.unitLine_bautin_mem_den_unstable` and `Line.PSC.angle_bautin_mem_den_unstable` the
  second Lyapunov coefficient therefore takes both signs on the Bautin set of `Line.PSC`: the zero
  set of `𝔅_P` is not decided by one sign, and the codimension-three points `ℓ₁ = ℓ₂ = 0` (where
  `ℓ₃` decides) are not located here.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace PSC

open Complex Matrix Filter Topology Asymptotics
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold
open powerlib.Dynamics.Degenerate
open powerlib.Dynamics.Degenerate.PlanarFocus (frameX frameY Jet5)

namespace BautinStable

open Bautin (pv lowF1 lowF2 lowF3)

/-- **A locally asymptotically stable Bautin point**: `E = R = L = 1`, `ω₀ = 5`, `V = 5√2/4`,
`K_p = 52/5`, `P_ref = −1/4`, `δ* = −π/4` (`κ = K_p Q = 0`, `t = −13`). -/
def bpt : Model := ⟨⟨⟨1, 5 * Real.sqrt 2 / 4, 1, 1, 5⟩, 52 / 5, -1 / 4⟩, -(Real.pi / 4)⟩

@[tmio M, powerlib_domain] private theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

/-- The operating angle `δ* = −π/4`, `cos δ* = √2/2`, `sin δ* = −√2/2`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bpt_trig :
    Real.cos bpt.δ = Real.sqrt 2 / 2 ∧ Real.sin bpt.δ = -(Real.sqrt 2 / 2) :=
  ⟨by rw [show bpt.δ = -(Real.pi / 4) from rfl, Real.cos_neg, Real.cos_pi_div_four],
    by rw [show bpt.δ = -(Real.pi / 4) from rfl, Real.sin_neg, Real.sin_pi_div_four]⟩

/-- The model is physical. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_physical : Meets bpt .physical :=
  ⟨⟨by norm_num [bpt], by simp only [bpt]; positivity, by norm_num [bpt], by norm_num [bpt],
    by norm_num [bpt]⟩, by norm_num [bpt]⟩

/-- The angle is balanced, `P(−π/4) = −1/4`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_balanced : Meets bpt .balanced := by
  change bpt.g.qssPower bpt.δ = -1 / 4
  rw [Network.qssPower_eq _ (by norm_num [bpt, Network.absSq, Network.X]), bpt_trig.1,
    bpt_trig.2]
  simp only [bpt, Network.absSq, Network.X]
  linear_combination (-15 / 104) * sqrt2_sq

/-- The reactive power at the point, `Q = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_Q : bpt.Q = 0 := by
  change bpt.g.qssReactive bpt.δ = 0
  rw [Network.qssReactive_eq _ (by norm_num [bpt, Network.absSq, Network.X]), bpt_trig.1,
    bpt_trig.2]
  simp only [bpt, Network.absSq, Network.X]
  linear_combination (-5 / 52) * sqrt2_sq

/-- The monic cubic at the point: `a₂ = 2`, `a₁ = 26`, `a₀ = 52`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_coeffs :
    bpt.g.coeff2 bpt.Q = 2 ∧ bpt.g.coeff1 bpt.Q = 26 ∧ bpt.g.coeff0 bpt.Q = 52 := by
  rw [bpt_Q]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X, bpt]

/-- The angle term `t = −13`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_angleShift : bpt.angleShift = -13 := by
  rw [Model.angleShift, bpt_Q]
  norm_num [bpt]

/-- **The point is degenerate**: on the Hopf boundary with a critical pair at `ω = √26`, and every
critical pair has `ℓ₁ = 0` (`𝔅_P(0, 1, 5, −13) = 0`, `Line.PSC.Model.sign_firstLyapunov_crit`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_firstLyapunov :
    (∃ q p : Fin 3 → ℂ, IsCriticalPair bpt.field 0 (Real.sqrt 26) q p) ∧
      ∀ ω (q p : Fin 3 → ℂ), IsCriticalPair bpt.field 0 ω q p →
        firstLyapunov bpt.field 0 ω q p = 0 := by
  obtain ⟨h2, h1, h0⟩ := bpt_coeffs
  have hH : bpt.g.coeff2 bpt.Q * bpt.g.coeff1 bpt.Q = bpt.g.coeff0 bpt.Q := by
    rw [h2, h1, h0]; norm_num
  have h1p : 0 < bpt.g.coeff1 bpt.Q := by rw [h1]; norm_num
  have h0p : 0 < bpt.g.coeff0 bpt.Q := by rw [h0]; norm_num
  refine ⟨?_, fun ω q p hcp => ?_⟩
  · have h := bpt.exists_isCriticalPair_of_boundary bpt_physical bpt_balanced h1p h0p hH
    rwa [h1] at h
  · have hs := Model.sign_firstLyapunov_crit bpt_physical bpt_balanced hH h1p h0p hcp
    have hB : bautinForm (bpt.g.Kp * bpt.Q) (bpt.g.R / bpt.g.L) bpt.g.ω0 bpt.angleShift = 0 := by
      rw [bpt_angleShift, bpt_Q]
      norm_num [bautinForm, bautinG, bautinH, bpt]
    rw [hB, sign_zero, neg_zero] at hs
    exact sign_eq_zero_iff.mp hs

/-- The linear part of the rotated frame, componentwise:
`J_rot = [[0, −52/5, 0], [0, −1, 5], [1, −5, −1]]`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotJ_apply (z : State 3) (i : Fin 3) :
    bpt.rotJ z i = ![-(52 / 5) * z 1, -z 1 + 5 * z 2, z 0 - 5 * z 1 - z 2] i := by
  rw [Model.rotJ, Dynamics.toEuclideanCLM_apply3, bpt_Q]
  fin_cases i <;> norm_num [bpt]
  ring

/-- The linear part in the rotated frame: `DF(0) R_{−π/4} = R_{−π/4} J_rot`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem fderiv_rotT (z : State 3) :
    fderiv ℝ bpt.field 0 (rotT bpt.δ z) = rotT bpt.δ (bpt.rotJ z) :=
  bpt.fderiv_field_rotT (by norm_num [bpt]) z

/-- The nonlinear part of the rotated field. -/
def frot (z : State 3) : State 3 := bpt.rotField z - bpt.rotJ z

/-- **The nonlinearities of the rotated field**:
`f_rot = ((13/5)(cos z₀ − 1) − (52/5)((cos z₀ − 1) z₁ + sin z₀ z₂), cos z₀ − 1, sin z₀ − z₀)`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem frot_apply (z : State 3) (i : Fin 3) :
    frot z i = ![13 / 5 * (Real.cos (z 0) - 1) - 52 / 5 * ((Real.cos (z 0) - 1) * z 1 +
      Real.sin (z 0) * z 2), Real.cos (z 0) - 1, Real.sin (z 0) - z 0] i := by
  rw [frot, PiLp.sub_apply, rotJ_apply]
  fin_cases i
  · simp [Model.rotField, bpt_Q]; norm_num [bpt]; ring
  · simp [Model.rotField, bpt_Q]; norm_num [bpt]
  · simp [Model.rotField, bpt_Q]; norm_num [bpt]

/-- The nonlinear part `f = F − DF(0)` of the grid-frame field. -/
def fnl (x : State 3) : State 3 := bpt.field x - fderiv ℝ bpt.field 0 x

/-- **The nonlinear part in the rotated frame**: `f(R_{−π/4} z) = R_{−π/4} f_rot(z)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem fnl_rotT (z : State 3) :
    fnl (rotT bpt.δ z) = rotT bpt.δ (frot z) := by
  rw [fnl, Model.field_rotT bpt_physical bpt_balanced, fderiv_rotT, frot, map_sub]

/-- `r = √26`, the Hopf frequency. -/
def r : ℝ := Real.sqrt 26

/-- `√26 > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem r_pos : 0 < r := Real.sqrt_pos.mpr (by norm_num)

/-- `(√26)² = 26`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem r_sq : r ^ 2 = 26 := Real.sq_sqrt (by norm_num)

/-- The right critical vector of the rotated frame, `q = (2√26 i, 5, 1 + √26 i)`. -/
def qv : Fin 3 → ℂ := ![2 * (r : ℂ) * I, 5, 1 + (r : ℂ) * I]

/-- The left critical vector of the rotated frame, `⟨p, q⟩ = 1`. -/
def pv3 : Fin 3 → ℂ :=
  ![-1 / 60 + (r : ℂ) / 780 * I, 7 / 75 - (r : ℂ) / 300 * I, 1 / 30 + (r : ℂ) / 60 * I]

/-- The rotated-frame critical vector is `critVecQ 1 1 5 √26`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critQ_eq : bpt.critQ r = rotC bpt.δ qv := by
  have hr : (r : ℂ) ^ 2 = 26 := by rw [← Complex.ofReal_pow, r_sq]; norm_num
  rw [Model.critQ]
  congr 1
  ext i
  fin_cases i <;> simp [critVecQ, qv, bpt]
  · ring_nf; simp only [Complex.I_sq, hr]; ring
  · ring

/-- The rotated-frame left vector is the normalised `critVecL` (`⟨p, q⟩ = 1`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem critP_eq : bpt.critP r = rotC bpt.δ pv3 := by
  have hr : (r : ℂ) ^ 2 = 26 := by rw [← Complex.ofReal_pow, r_sq]; norm_num
  have hr3 : (r : ℂ) ^ 3 = 26 * r := by rw [pow_succ, hr]
  have hI3 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  have hinv : (starRingEnd ℂ (critPairing 1 0 1 5 r))⁻¹ = -1 / 300 + (r : ℂ) / 3900 * I := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    simp [critPairing, map_mul, map_sub, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq, hr, hr3]
    ring
  rw [Model.critP, bpt_Q]
  have e : (bpt.g.E / bpt.g.L) = 1 ∧ bpt.g.Kp * 0 = 0 ∧ bpt.g.R / bpt.g.L = 1 ∧
      bpt.g.ω0 = 5 := by norm_num [bpt]
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2, hinv]
  congr 1
  ext i
  fin_cases i <;> simp [critVecL, pv3] <;> ring_nf <;> simp only [Complex.I_sq, hr, hr3, hI3] <;>
    ring

/-- **The critical pair at `ω = √26`**: `(R_{−π/4} q, R_{−π/4} p)`
(`Line.PSC.Model.isCriticalPair_crit`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCriticalPair_bpt :
    IsCriticalPair bpt.field 0 r (rotC bpt.δ qv) (rotC bpt.δ pv3) := by
  obtain ⟨h2, h1, h0⟩ := bpt_coeffs
  rw [← critQ_eq, ← critP_eq]
  exact Model.isCriticalPair_crit bpt_physical bpt_balanced (by rw [h2, h1, h0]; norm_num)
    r_pos (by rw [h1, r_sq])

/-- The rational chart `ι' y = y₀ a + y₁ b`, `a = Re q = (0, 5, 1)`, `b = Im q/√26 = (2, 0, 1)`. -/
def iotaR : State 2 →L[ℝ] State 3 :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (WithLp.toLp 2 ![0, 5, 1] : State 3) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (WithLp.toLp 2 ![2, 0, 1] : State 3)

/-- The rational coordinates `π' x = (⟨(−1/30, 14/75, 1/15), x⟩, ⟨(1/15, −13/75, 13/15), x⟩)`. -/
def piR : State 3 →L[ℝ] State 2 :=
  (innerSL ℝ (WithLp.toLp 2 ![-1 / 30, 14 / 75, 1 / 15] : State 3)).smulRight
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (innerSL ℝ (WithLp.toLp 2 ![1 / 15, -13 / 75, 13 / 15] : State 3)).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The reduced linear part in the rational chart, `(y₀, y₁) ↦ (y₁, −26 y₀)`. -/
def rotR : State 2 →L[ℝ] State 2 :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (-26 : ℝ) • (EuclideanSpace.proj (0 : Fin 2)).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The stable eigenvector `w = (26/5, 1, −1/5)` (`J_rot w = −2 w`), spanning `ker π'`. -/
def wv : State 3 := WithLp.toLp 2 ![26 / 5, 1, -1 / 5]

/-- The rational chart, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem iotaR_apply (y : State 2) (i : Fin 3) :
    iotaR y i = ![2 * y 1, 5 * y 0, y 0 + y 1] i := by
  fin_cases i <;> simp [iotaR] <;> ring

/-- The rational coordinates, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_apply (x : State 3) :
    piR x 0 = -1 / 30 * x 0 + 14 / 75 * x 1 + 1 / 15 * x 2 ∧
      piR x 1 = 1 / 15 * x 0 + -13 / 75 * x 1 + 13 / 15 * x 2 := by
  simp only [piR, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp
  constructor <;> ring

/-- The reduced linear part, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotR_apply (y : State 2) :
    rotR y 0 = y 1 ∧ rotR y 1 = -26 * y 0 := by
  simp [rotR]

/-- `rotR² = −(√26)²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotR_rotR (y : State 2) :
    rotR (rotR y) = -(r ^ 2) • y := by
  rw [r_sq]
  ext i; fin_cases i <;> simp [rotR]

/-- `π' ι' = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_iotaR (y : State 2) : piR (iotaR y) = y := by
  obtain ⟨h0, h1⟩ := piR_apply (iotaR y)
  ext i; fin_cases i
  · simp only [Fin.zero_eta, h0, iotaR_apply]; simp; ring
  · simp only [Fin.mk_one, h1, iotaR_apply]; simp; ring

/-- `w ∈ ker π'`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_wv : piR wv = 0 := by
  obtain ⟨h0, h1⟩ := piR_apply wv
  ext i; fin_cases i
  · rw [Fin.zero_eta, h0]; simp [wv]; norm_num
  · rw [Fin.mk_one, h1]; simp [wv]; norm_num

/-- `J_rot w = −2 w`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_wv : bpt.rotJ wv = (-2 : ℝ) • wv := by
  ext i; rw [rotJ_apply]; fin_cases i <;> simp [wv] <;> norm_num

/-- `π' J_rot ι' = rotR`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_A_iotaR (y : State 2) :
    piR (bpt.rotJ (iotaR y)) = rotR y := by
  obtain ⟨h0, h1⟩ := piR_apply (bpt.rotJ (iotaR y))
  obtain ⟨r0, r1⟩ := rotR_apply y
  ext i; fin_cases i
  · simp only [Fin.zero_eta, h0, r0, rotJ_apply, iotaR_apply]; simp; ring
  · simp only [Fin.mk_one, h1, r1, rotJ_apply, iotaR_apply]; simp; ring

/-- **The rational chart is a chart of the critical plane of the rotated frame**: `π' ι' = 1` and
`ι' π' = critP q p`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isChart_R : IsChart (critP qv pv3) iotaR piR := by
  refine ⟨piR_iotaR, fun x => ?_⟩
  obtain ⟨h0, h1⟩ := piR_apply x
  have hr : r ^ 2 = 26 := r_sq
  rw [critP, ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1]
  ext i
  rw [iotaR_apply]
  fin_cases i <;>
    simp [h0, h1, qv, pv3, reV_apply, imV_apply, PiLp.inner_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp only [hr] <;> ring_nf

/-- **`(1 − P) v = (v₁ − 5 (π' v)₀) w`**: the stable component of a vector. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem sub_iotaR_piR (v : State 3) :
    v - iotaR (piR v) = (v 1 - 5 * piR v 0) • wv := by
  obtain ⟨h0, h1⟩ := piR_apply v
  ext i
  fin_cases i <;> simp [iotaR_apply, h0, h1, wv] <;> ring

/-- The grid-frame chart `ι = R_{−π/4} ι'` of the critical plane. -/
def iotaG : State 2 →L[ℝ] State 3 := (rotT bpt.δ).comp iotaR

/-- The grid-frame coordinates `π = π' R_{π/4}`. -/
def piG : State 3 →L[ℝ] State 2 := piR.comp (rotT (-bpt.δ))

/-- `π (R_{−π/4} v) = π' v`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piG_rotT (v : State 3) : piG (rotT bpt.δ v) = piR v := by
  rw [piG, ContinuousLinearMap.comp_apply, rotT_neg_rotT]

/-- **The grid-frame chart is a chart of the critical plane**: `π ι = 1`, `ι π = critP q p`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isChart_G :
    IsChart (critP (rotC bpt.δ qv) (rotC bpt.δ pv3)) iotaG piG := by
  refine ⟨fun y => ?_, fun x => ?_⟩
  · rw [iotaG, ContinuousLinearMap.comp_apply, piG_rotT, piR_iotaR]
  · rw [critP_rotC, ← isChart_R.ι_π, iotaG, piG, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]

/-- **`(1 − P)` of a rotated vector**: `R v − ι π (R v) = R ((v₁ − 5 (π' v)₀) w)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem sub_iotaG_piG (v : State 3) :
    rotT bpt.δ v - iotaG (piG (rotT bpt.δ v)) = rotT bpt.δ ((v 1 - 5 * piR v 0) • wv) := by
  rw [piG_rotT, iotaG, ContinuousLinearMap.comp_apply, ← map_sub, sub_iotaR_piR]

/-! ## The approximate centre manifold (rotated frame) -/

/-- `h` of the manifold, degree 2. -/
def hL2 : List (ℝ × ℕ × ℕ × ℕ) := [(-3887 / 135, 2, 0, 0), (-299 / 135, 1, 1, 0), (-152 / 135, 0, 2,
    0)]

/-- `(26/5) h`, the angle part of the manifold, degree 2. -/
def aL2 : List (ℝ × ℕ × ℕ × ℕ) := [(-101062 / 675, 2, 0, 0), (-7774 / 675, 1, 1, 0), (-3952 / 675,
    0, 2, 0)]

/-- `−h/5`, the `i_q` part of the manifold, degree 2. -/
def cL2 : List (ℝ × ℕ × ℕ × ℕ) := [(3887 / 675, 2, 0, 0), (299 / 675, 1, 1, 0), (152 / 675, 0, 2,
    0)]

/-- `h` of the manifold, degree 3. -/
def hL3 : List (ℝ × ℕ × ℕ × ℕ) := [(152168614 / 401625, 3, 0, 0), (23089456 / 1204875, 2, 1, 0),
    (16888651 / 1204875, 1, 2, 0), (-228863 / 1204875, 0, 3, 0)]

/-- `(26/5) h`, the angle part of the manifold, degree 3. -/
def aL3 : List (ℝ × ℕ × ℕ × ℕ) := [(3956383964 / 2008125, 3, 0, 0), (600325856 / 6024375, 2, 1, 0),
    (439104926 / 6024375, 1, 2, 0), (-5950438 / 6024375, 0, 3, 0)]

/-- `−h/5`, the `i_q` part of the manifold, degree 3. -/
def cL3 : List (ℝ × ℕ × ℕ × ℕ) := [(-152168614 / 2008125, 3, 0, 0), (-23089456 / 6024375, 2, 1, 0),
    (-16888651 / 6024375, 1, 2, 0), (228863 / 6024375, 0, 3, 0)]

/-- `h` of the manifold, degree 4. -/
def hL4 : List (ℝ × ℕ × ℕ × ℕ) := [(-2858887182307 / 325316250, 4, 0, 0), (-45621876001 / 162658125,
    3, 1, 0), (-7600571693 / 15491250, 2, 2, 0), (-473213 / 325316250, 1, 3, 0), (-162649127 /
    26025300, 0, 4, 0)]

/-- `(26/5) h`, the angle part of the manifold, degree 4. -/
def aL4 : List (ℝ × ℕ × ℕ × ℕ) := [(-37165533369991 / 813290625, 4, 0, 0), (-1186168776026 /
    813290625, 3, 1, 0), (-98807432009 / 38728125, 2, 2, 0), (-6151769 / 813290625, 1, 3, 0),
    (-2114438651 / 65063250, 0, 4, 0)]

/-- `−h/5`, the `i_q` part of the manifold, degree 4. -/
def cL4 : List (ℝ × ℕ × ℕ × ℕ) := [(2858887182307 / 1626581250, 4, 0, 0), (45621876001 / 813290625,
    3, 1, 0), (7600571693 / 77456250, 2, 2, 0), (473213 / 1626581250, 1, 3, 0), (162649127 /
    130126500, 0, 4, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low1L4 : List (ℝ × ℕ × ℕ × ℕ) := [(-40, 1, 1, 0), (-40, 0, 2, 0), (404248 / 135, 3, 0, 0),
    (404248 / 135, 2, 1, 0), (71512 / 135, 1, 2, 0), (4864 / 45, 0, 3, 0), (-240303342968 /
    10843875, 4, 0, 0), (-711977888128 / 10843875, 3, 1, 0), (-19164452632 / 3614625, 2, 2, 0),
    (-1064877712 / 433755, 1, 3, 0), (284466736 / 10843875, 0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low1L5 : List (ℝ × ℕ × ℕ × ℕ) := [(1285784880243188 / 813290625, 5, 0, 0), (252748768786072 /
    162658125, 4, 1, 0), (31159928240428 / 162658125, 3, 2, 0), (12270479150852 / 162658125, 2, 3,
    0), (77288802862 / 32531625, 1, 4, 0), (517872260608 / 813290625, 0, 5, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low2L4 : List (ℝ × ℕ × ℕ × ℕ) := [(-2, 0, 2, 0), (202124 / 675, 2, 1, 0), (15548 / 675, 1, 2,
    0), (7904 / 675, 0, 3, 0), (-5106763922 / 455625, 4, 0, 0), (-307137796628 / 54219375, 3, 1, 0),
    (-20643332762 / 18073125, 2, 2, 0), (-2311981516 / 10843875, 1, 3, 0), (-786034954 / 54219375,
    0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low2L5 : List (ℝ × ℕ × ℕ × ℕ) := [(399840076169768 / 1355484375, 5, 0, 0), (2057240204578 /
    15946875, 4, 1, 0), (1437497750312 / 54219375, 3, 2, 0), (1674833767958 / 271096875, 2, 3, 0),
    (108446721682 / 271096875, 1, 4, 0), (69681420133 / 1355484375, 0, 5, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low3L4 : List (ℝ × ℕ × ℕ × ℕ) := [(-4 / 3, 0, 3, 0), (202124 / 675, 2, 2, 0), (15548 / 675, 1,
    3, 0), (7904 / 675, 0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low3L5 : List (ℝ × ℕ × ℕ × ℕ) := [(-10213527844 / 455625, 4, 1, 0), (-16025234368 / 2168775, 3,
    2, 0), (-37684710388 / 18073125, 2, 3, 0), (-15215926492 / 54219375, 1, 4, 0), (-1737011792 /
    54219375, 0, 5, 0)]

/-- The jet of the first chart coordinate, degree 2. -/
def cF2 : List (ℝ × ℕ × ℕ × ℕ) := [(52 / 75, 1, 1, 0), (37 / 75, 0, 2, 0)]

/-- The jet of the second chart coordinate, degree 2. -/
def cG2 : List (ℝ × ℕ × ℕ × ℕ) := [(-104 / 75, 1, 1, 0), (-104 / 75, 0, 2, 0)]

/-- The jet of the first chart coordinate, degree 3. -/
def cF3 : List (ℝ × ℕ × ℕ × ℕ) := [(-2627612 / 50625, 3, 0, 0), (-1111682 / 50625, 2, 1, 0),
    (-348218 / 50625, 1, 2, 0), (-1484 / 1875, 0, 3, 0)]

/-- The jet of the second chart coordinate, degree 3. -/
def cG3 : List (ℝ × ℕ × ℕ × ℕ) := [(5255224 / 50625, 3, 0, 0), (5255224 / 50625, 2, 1, 0), (929656 /
    50625, 1, 2, 0), (43732 / 16875, 0, 3, 0)]

/-- The jet of the first chart coordinate, degree 4. -/
def cF4 : List (ℝ × ℕ × ℕ × ℕ) := [(-2995815071093 / 4066453125, 4, 0, 0), (2324322798122 /
    4066453125, 3, 1, 0), (-3196703107 / 1355484375, 2, 2, 0), (3703511474 / 162658125, 1, 3, 0),
    (-4569851939 / 4066453125, 0, 4, 0)]

/-- The jet of the second chart coordinate, degree 4. -/
def cG4 : List (ℝ × ℕ × ℕ × ℕ) := [(-3123943458584 / 4066453125, 4, 0, 0), (-9255712545664 /
    4066453125, 3, 1, 0), (102633672284 / 1355484375, 2, 2, 0), (-10596288196 / 162658125, 1, 3, 0),
    (44965839568 / 4066453125, 0, 4, 0)]

/-- The jet of the first chart coordinate, degree 5. -/
def cF5 : List (ℝ × ℕ × ℕ × ℕ) := [(638799992239058 / 304983984375, 5, 0, 0), (-947128354866083 /
    60996796875, 4, 1, 0), (-70868351092682 / 60996796875, 3, 2, 0), (-50553414538783 / 60996796875,
    2, 3, 0), (-34657981202 / 1742765625, 1, 4, 0), (-699919189417 / 87138281250, 0, 5, 0)]

/-- The jet of the second chart coordinate, degree 5. -/
def cG5 : List (ℝ × ℕ × ℕ × ℕ) := [(16715203443161444 / 304983984375, 5, 0, 0), (2100709426118836 /
    60996796875, 4, 1, 0), (14463979405564 / 60996796875, 3, 2, 0), (49288451076176 / 60996796875,
    2, 3, 0), (-1962351228734 / 12199359375, 1, 4, 0), (-1735593098096 / 304983984375, 0, 5, 0)]

/-- The polynomial part of the defect, degrees five to eight. -/
def highD : List (ℝ × ℕ × ℕ × ℕ) := [(-3477220422209768 / 60996796875, 5, 0, 0), (-2807858653492204
    / 60996796875, 4, 1, 0), (-454630361011502 / 20332265625, 3, 2, 0), (-42727279815649 /
    60996796875, 2, 3, 0), (-31351548377981 / 60996796875, 1, 4, 0), (128345017151 / 5809218750, 0,
    5, 0), (234672053270899088 / 130707421875, 6, 0, 0), (1879142195925100496 / 2744855859375, 5, 1,
    0), (560456068871867246 / 2744855859375, 4, 2, 0), (92818312442378666 / 2744855859375, 3, 3, 0),
    (6251303966813737 / 2744855859375, 2, 4, 0), (871709894467633 / 2744855859375, 1, 5, 0),
    (-177821130432686 / 2744855859375, 0, 6, 0)]

/-- `h`, degrees two to four. -/
def hL : List (ℝ × ℕ × ℕ × ℕ) := hL2 ++ hL3 ++ hL4

/-- The graph in the rotated chart coordinates, `H(y) = h(y) w`. -/
def manifoldH (y : State 2) : State 3 := poly3 hL (y 0) (y 1) 0 • wv

/-- The graph in grid coordinates, `R_{−π/4} H(y)`. -/
def manifoldG (y : State 2) : State 3 := rotT bpt.δ (manifoldH y)

/-- **The order-four approximate centre manifold** `φ(x) = R_{−π/4} H(π x)`. -/
def manifold (x : State 3) : State 3 := manifoldG (piG x)

/-- `π' H(y) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_manifoldH (y : State 2) : piR (manifoldH y) = 0 := by
  simp [manifoldH, map_smul, piR_wv]

/-- The derivative of `H`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_manifoldH (y : State 2) :
    ∃ L : State 2 →L[ℝ] State 3, HasFDerivAt manifoldH L y ∧ ∀ v, L v =
      dpoly3 hL (y 0) (y 1) 0 (v 0) (v 1) 0 • wv := by
  obtain ⟨L1, h1, hv1⟩ := Dynamics.Degenerate.hasFDerivAt_poly3 hL (Dynamics.coord 0)
    (Dynamics.coord 1) 0 y
  have e : manifoldH = fun z => poly3 hL (Dynamics.coord 0 z) (Dynamics.coord 1 z)
      ((0 : State 2 →L[ℝ] ℝ) z) • wv := by
    funext z; simp [manifoldH]
  refine ⟨L1.smulRight wv, ?_, fun v => ?_⟩
  · rw [e]; exact h1.smul_const wv
  · simp [hv1]

/-- The derivative of the grid-frame graph `R_{−π/4} H`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_manifoldG (y : State 2) :
    ∃ L : State 2 →L[ℝ] State 3, HasFDerivAt manifoldG L y ∧ ∀ v, L v =
      rotT bpt.δ (dpoly3 hL (y 0) (y 1) 0 (v 0) (v 1) 0 • wv) := by
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldH y
  exact ⟨(rotT bpt.δ).comp L, (rotT bpt.δ).hasFDerivAt.comp y hL', fun v => by simp [hLv]⟩

/-- `φ` is `C¹`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem contDiffAt_manifold : ContDiffAt ℝ 1 manifold 0 := by
  have h1 := Dynamics.Degenerate.contDiff_poly3 hL ((Dynamics.coord 0).comp piG)
    ((Dynamics.coord 1).comp piG) 0 (k := 1)
  have e : manifold = fun x => rotT bpt.δ (poly3 hL ((Dynamics.coord 0).comp piG x)
      ((Dynamics.coord 1).comp piG x) ((0 : State 3 →L[ℝ] ℝ) x) • wv) := by
    funext x; simp [manifold, manifoldG, manifoldH]
  rw [e]
  exact ((rotT bpt.δ).contDiff.comp (h1.smul contDiff_const)).contDiffAt

/-- `φ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem manifold_zero : manifold 0 = 0 := by
  simp [manifold, manifoldG, manifoldH, hL, hL2, hL3, hL4]

/-- `Dφ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fderiv_manifold_zero : fderiv ℝ manifold 0 = 0 := by
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldG (piG 0)
  have hc : HasFDerivAt manifold (L.comp piG) 0 := hL'.comp (0 : State 3) piG.hasFDerivAt
  rw [hc.fderiv]
  ext v i
  simp [hLv, hL, hL2, hL3, hL4]

/-- `φ` takes values in `ker P`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critP_manifold (x : State 3) :
    critP (rotC bpt.δ qv) (rotC bpt.δ pv3) (manifold x) = 0 := by
  rw [← isChart_G.ι_π, manifold, manifoldG, piG_rotT, piR_manifoldH, map_zero]

/-! ## The chart field -/

/-- The point `ι' y + H(y)` of the manifold over `y`, in the rotated frame. -/
def chartPt (y : State 2) : State 3 := iotaR y + manifoldH y

/-- The grid-frame point of the manifold over `y`: `ι y + φ(ι y) = R_{−π/4} (ι' y + H y)`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem iotaG_add_manifold (y : State 2) :
    iotaG y + manifold (iotaG y) = rotT bpt.δ (chartPt y) := by
  rw [manifold, isChart_G.left_inv, iotaG, ContinuousLinearMap.comp_apply, manifoldG, chartPt,
    map_add]

/-- **The chart field** of the manifold: `rotR y + π' f_rot(ι' y + H y)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem chartField_eq (y : State 2) :
    chartField (fderiv ℝ bpt.field 0) fnl manifold iotaG piG y =
      rotR y + piR (frot (chartPt y)) := by
  have hA : fderiv ℝ bpt.field 0 (iotaG y) = rotT bpt.δ (bpt.rotJ (iotaR y)) := by
    rw [iotaG, ContinuousLinearMap.comp_apply, fderiv_rotT]
  rw [chartField, iotaG_add_manifold, hA, fnl_rotT, ← map_add, piG_rotT, map_add, piR_A_iotaR]

/-- The linear part of the angle over `y`. -/
def lin0 (y : State 2) : ℝ := 2 * y 1

/-- The linear part of `i_d` over `y`. -/
def lin1 (y : State 2) : ℝ := 5 * y 0

/-- The linear part of `i_q` over `y`. -/
def lin2 (y : State 2) : ℝ := y 0 + y 1

/-- The angle `x₀` of the manifold over `y`. -/
def tv (y : State 2) : ℝ := lin0 y + pv aL2 y + pv aL3 y + pv aL4 y

/-- The current `x₁` of the manifold over `y`. -/
def x1v (y : State 2) : ℝ := lin1 y + pv hL2 y + pv hL3 y + pv hL4 y

/-- The current `x₂` of the manifold over `y`. -/
def x2v (y : State 2) : ℝ := lin2 y + pv cL2 y + pv cL3 y + pv cL4 y

/-- The components of `ι' y + H(y)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem chartPt_apply (y : State 2) :
    chartPt y 0 = tv y ∧ chartPt y 1 = x1v y ∧ chartPt y 2 = x2v y := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [chartPt, PiLp.add_apply, iotaR_apply, manifoldH, PiLp.smul_apply, smul_eq_mul,
      wv, tv, x1v, x2v, lin0, lin1, lin2, pv, hL, hL2, hL3, hL4, aL2, aL3, aL4, cL2, cL3, cL4,
      poly3_cons, poly3_nil, List.cons_append, List.nil_append] <;>
    simp <;> ring

/-- The first chart coordinate of `f_rot` on the manifold. -/
def G0 (y : State 2) : ℝ := piR (frot (chartPt y)) 0

/-- The second chart coordinate of `f_rot` on the manifold. -/
def G1 (y : State 2) : ℝ := piR (frot (chartPt y)) 1

/-- The droop nonlinearity `−20((cos x₀ − 1) x₁ + sin x₀ · x₂)` on the manifold. -/
def f0v (y : State 2) : ℝ :=
  -20 * ((Real.cos (tv y) - 1) * x1v y + Real.sin (tv y) * x2v y)

/-- The chart coordinates of `f_rot` on the manifold (`f_rot,0 = (13/5)(cos x₀ − 1) + (13/25) f₀`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem G_eq (y : State 2) :
    G0 y = -13 / 750 * f0v y + 1 / 10 * (Real.cos (tv y) - 1) +
        1 / 15 * (Real.sin (tv y) - tv y) ∧
      G1 y = 13 / 375 * f0v y + 13 / 15 * (Real.sin (tv y) - tv y) := by
  obtain ⟨c0, c1, c2⟩ := chartPt_apply y
  obtain ⟨g0, g1⟩ := piR_apply (frot (chartPt y))
  simp only [G0, G1, g0, g1, frot_apply, f0v]
  simp [c0, c1, c2]
  constructor <;> ring

/-! ## Orders of the pieces -/

@[tmio M, powerlib_domain] private theorem tendsto_norm0 :
    Tendsto (fun y : State 2 => ‖y‖) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_norm (E := State 2)).tendsto 0

@[tmio M, powerlib_domain] private theorem coord_isBigO (i : Fin 2) :
    (fun y : State 2 => y i) =O[𝓝 0] fun y => ‖y‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, norm_norm, one_mul]; exact Dynamics.abs_apply_le_norm y i)

@[tmio M, powerlib_domain] private theorem pv_isBigO (L : List (ℝ × ℕ × ℕ × ℕ)) {k : ℕ}
    (hL : ∀ t ∈ L, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) :
    (fun y => pv L y) =O[𝓝 0] fun y => ‖y‖ ^ k :=
  Dynamics.Degenerate.isBigO_poly3_weight tendsto_norm0 (coord_isBigO 0) (coord_isBigO 1)
    (isBigO_zero _ _) L hL

@[tmio M, powerlib_domain] private theorem mono {f : State 2 → ℝ} {a b : ℕ}
    (h : f =O[𝓝 0] fun y => ‖y‖ ^ a) (hb : b ≤ a) : f =O[𝓝 0] fun y => ‖y‖ ^ b :=
  h.trans (Dynamics.isBigO_pow_of_tendsto tendsto_norm0 hb)

@[tmio M, powerlib_domain] private theorem lin_isBigO (c₀ c₁ : ℝ) :
    (fun y : State 2 => c₀ * y 0 + c₁ * y 1) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (((coord_isBigO 0).const_mul_left c₀).add ((coord_isBigO 1).const_mul_left c₁)).congr_right
    fun _ => (pow_one _).symm

@[tmio M, powerlib_domain] private theorem o_l0 :
    (fun y : State 2 => lin0 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (lin_isBigO 0 2).congr_left fun y => by simp only [lin0]; ring

@[tmio M, powerlib_domain] private theorem o_l1 :
    (fun y : State 2 => lin1 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (lin_isBigO 5 0).congr_left fun y => by simp only [lin1]; ring

@[tmio M, powerlib_domain] private theorem o_l2 :
    (fun y : State 2 => lin2 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (lin_isBigO 1 1).congr_left fun y => by simp only [lin2]; ring

@[tmio M, powerlib_domain] private theorem o_a2 :
   (fun y : State 2 => pv aL2 y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 pv_isBigO _ (by simp [aL2])

@[tmio M, powerlib_domain] private theorem o_a3 :
   (fun y : State 2 => pv aL3 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 pv_isBigO _ (by simp [aL3])

@[tmio M, powerlib_domain] private theorem o_a4 :
   (fun y : State 2 => pv aL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
 pv_isBigO _ (by simp [aL4])

@[tmio M, powerlib_domain] private theorem o_b2 :
   (fun y : State 2 => pv hL2 y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 pv_isBigO _ (by simp [hL2])

@[tmio M, powerlib_domain] private theorem o_b3 :
   (fun y : State 2 => pv hL3 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 pv_isBigO _ (by simp [hL3])

@[tmio M, powerlib_domain] private theorem o_b4 :
   (fun y : State 2 => pv hL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
 pv_isBigO _ (by simp [hL4])

@[tmio M, powerlib_domain] private theorem o_c2 :
   (fun y : State 2 => pv cL2 y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 pv_isBigO _ (by simp [cL2])

@[tmio M, powerlib_domain] private theorem o_c3 :
   (fun y : State 2 => pv cL3 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 pv_isBigO _ (by simp [cL3])

@[tmio M, powerlib_domain] private theorem o_c4 :
   (fun y : State 2 => pv cL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
 pv_isBigO _ (by simp [cL4])

@[tmio M, powerlib_domain] private theorem o_r :
   (fun y : State 2 => pv aL2 y + pv aL3 y + pv aL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 ((o_a2.add (mono o_a3 (by norm_num))).add (mono o_a4 (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_r3 :
   (fun y : State 2 => pv aL3 y + pv aL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 (o_a3.add (mono o_a4 (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_B :
   (fun y : State 2 => pv hL2 y + pv hL3 y + pv hL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 ((o_b2.add (mono o_b3 (by norm_num))).add (mono o_b4 (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_B3 :
   (fun y : State 2 => pv hL3 y + pv hL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 (o_b3.add (mono o_b4 (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_C :
   (fun y : State 2 => pv cL2 y + pv cL3 y + pv cL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 ((o_c2.add (mono o_c3 (by norm_num))).add (mono o_c4 (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_C3 :
   (fun y : State 2 => pv cL3 y + pv cL4 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 (o_c3.add (mono o_c4 (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_u :
   (fun y : State 2 => tv y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
 (((o_l0.add (mono o_a2 (by norm_num))).add (mono o_a3 (by norm_num))).add (mono o_a4 (by
    norm_num)))

@[tmio M, powerlib_domain] private theorem o_X1 :
   (fun y : State 2 => x1v y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
 (((o_l1.add (mono o_b2 (by norm_num))).add (mono o_b3 (by norm_num))).add (mono o_b4 (by
    norm_num)))

@[tmio M, powerlib_domain] private theorem o_X2 :
   (fun y : State 2 => x2v y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
 (((o_l2.add (mono o_c2 (by norm_num))).add (mono o_c3 (by norm_num))).add (mono o_c4 (by
    norm_num)))

/-! ## The nonlinearities minus their weight-five truncations -/

/-- The weight-five truncation of `f₀`. -/
def low1L : List (ℝ × ℕ × ℕ × ℕ) := low1L4 ++ low1L5

/-- The weight-five truncation of `cos x₀ − 1`. -/
def low2L : List (ℝ × ℕ × ℕ × ℕ) := low2L4 ++ low2L5

/-- The weight-five truncation of `sin x₀ − x₀`. -/
def low3L : List (ℝ × ℕ × ℕ × ℕ) := low3L4 ++ low3L5

/-- The weight-five truncation of `f₀` in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem low1_eq (y : State 2) :
    lowF1 (lin0 y) (pv aL2 y) (pv aL3 y) (pv aL4 y) (lin1 y) (pv hL2 y) (pv hL3 y) (lin2 y)
      (pv cL2 y) (pv cL3 y) (pv cL4 y) = pv low1L y := by
  simp only [lowF1, lin0, lin1, lin2, pv, aL2, aL3, aL4, hL2, hL3, cL2, cL3, cL4, low1L, low1L4,
    low1L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `cos x₀ − 1` in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem low2_eq (y : State 2) :
    lowF2 (lin0 y) (pv aL2 y) (pv aL3 y) (pv aL4 y) = pv low2L y := by
  simp only [lowF2, lin0, pv, aL2, aL3, aL4, low2L, low2L4, low2L5, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `sin x₀ − x₀` in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem low3_eq (y : State 2) :
    lowF3 (lin0 y) (pv aL2 y) (pv aL3 y) = pv low3L y := by
  simp only [lowF3, lin0, pv, aL2, aL3, low3L, low3L4, low3L5, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The Taylor polynomial of `f₀` minus its weight-five part is `O(‖y‖⁶)` (products of pieces of
total weight at least six). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem split1_isBigO :
    (fun y : State 2 => -20 * ((1 - tv y ^ 2 / 2 + tv y ^ 4 / 24 - 1) * x1v y +
      (tv y - tv y ^ 3 / 6 + tv y ^ 5 / 120) * x2v y) - lowF1 (lin0 y) (pv aL2 y) (pv aL3 y)
      (pv aL4 y) (lin1 y) (pv hL2 y) (pv hL3 y) (lin2 y) (pv cL2 y) (pv cL3 y) (pv cL4 y))
      =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((((((((((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 o_l0 o_a4 (by norm_num)) o_X1 (by
    norm_num)).const_mul_left 20).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 o_a2 o_a3 (by norm_num)) o_X1 (by
    norm_num)).const_mul_left 20)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_a2 o_a4 (by norm_num)) o_X1 (by
    norm_num)).const_mul_left 20)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_r3 o_r3 (by norm_num)) o_X1 (by
    norm_num)).const_mul_left 10)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 o_l0 o_l0 (by norm_num)) o_b4 (by
    norm_num)).const_mul_left 10)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_l0 o_a2 (by norm_num)) o_B3 (by
    norm_num)).const_mul_left 20)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 o_l0 o_a3 (by norm_num)) o_B (by
    norm_num)).const_mul_left 20)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 o_a2 o_a2 (by norm_num)) o_B (by
    norm_num)).const_mul_left 10)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_r o_u (by norm_num)) o_u (by norm_num)) o_u
    (by norm_num)) o_X1 (by norm_num)).const_mul_left (-5 / 6))).add ((Dynamics.isBigO_mul_pow (k :=
    6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k :=
    4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_r o_u (by norm_num)) o_u (by
    norm_num)) o_l0 (by norm_num)) o_X1 (by norm_num)).const_mul_left (-5 / 6))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_r o_u (by norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)) o_X1 (by
    norm_num)).const_mul_left (-5 / 6))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_r o_l0 (by norm_num)) o_l0 (by norm_num)) o_l0
    (by norm_num)) o_X1 (by norm_num)).const_mul_left (-5 / 6))).add ((Dynamics.isBigO_mul_pow (k :=
    6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k :=
    3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 o_l0 o_l0 (by norm_num)) o_l0
    (by norm_num)) o_l0 (by norm_num)) o_B (by norm_num)).const_mul_left (-5 / 6))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_a2 o_c4 (by norm_num)).const_mul_left
    (-20))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_a3 o_C3 (by
    norm_num)).const_mul_left (-20))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_a4 o_C
    (by norm_num)).const_mul_left (-20))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    o_l0 o_l0 (by norm_num)) o_r3 (by norm_num)) o_X2 (by norm_num)).const_mul_left 10)).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_l0 o_r (by norm_num)) o_r (by norm_num)) o_X2
    (by norm_num)).const_mul_left 10)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    o_r o_r (by norm_num)) o_r (by norm_num)) o_X2 (by norm_num)).const_mul_left (10 / 3))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 o_l0 o_l0 (by norm_num)) o_l0 (by norm_num))
    o_C3 (by norm_num)).const_mul_left (10 / 3))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 o_l0 o_l0 (by norm_num)) o_a2 (by norm_num)) o_C (by norm_num)).const_mul_left
    10)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 o_u o_u (by norm_num)) o_u (by
    norm_num)) o_u (by norm_num)) o_u (by norm_num)) o_X2 (by norm_num)).const_mul_left (-1 /
    6))).congr_left fun y => ?_
  simp only [tv, x1v, x2v, lowF1]
  ring

/-- The Taylor polynomial of `cos x₀ − 1` minus its weight-five part is `O(‖y‖⁶)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem split2_isBigO :
    (fun y : State 2 => 1 - tv y ^ 2 / 2 + tv y ^ 4 / 24 - 1 - lowF2 (lin0 y) (pv aL2 y)
      (pv aL3 y) (pv aL4 y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_a2 o_a4 (by
    norm_num)).const_mul_left (-1)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 o_r3 o_r3
    (by norm_num)).const_mul_left ((-1 / 2)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    o_l0 o_l0 (by norm_num)) o_l0 (by norm_num)) o_r3 (by norm_num)).const_mul_left ((1 / 6)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 o_l0 o_l0 (by norm_num)) o_r (by norm_num)) o_r
    (by norm_num)).const_mul_left ((1 / 4)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_l0 o_r (by norm_num)) o_r (by norm_num)) o_r (by norm_num)).const_mul_left ((1 / 6)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 o_r o_r (by norm_num)) o_r (by norm_num)) o_r
    (by norm_num)).const_mul_left ((1 / 24)))).congr_left fun y => ?_
  simp only [tv, lowF2]
  ring

/-- The Taylor polynomial of `sin x₀ − x₀` minus its weight-five part is `O(‖y‖⁶)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem split3_isBigO :
    (fun y : State 2 => tv y - tv y ^ 3 / 6 + tv y ^ 5 / 120 - tv y - lowF3 (lin0 y) (pv aL2 y)
      (pv aL3 y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 o_l0 o_l0 (by norm_num)) o_a4 (by norm_num)).const_mul_left ((-1 / 2))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_l0 o_a2 (by norm_num)) o_a3 (by norm_num)).const_mul_left (-1))).add ((Dynamics.isBigO_mul_pow
    (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_l0 o_a2 (by norm_num))
    o_a4 (by norm_num)).const_mul_left (-1))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 o_l0 o_r3 (by norm_num)) o_r3 (by
    norm_num)).const_mul_left ((-1 / 2)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 o_r o_r (by norm_num)) o_r (by
    norm_num)).const_mul_left ((-1 / 6)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_r o_u (by norm_num)) o_u (by norm_num)) o_u
    (by norm_num)) o_u (by norm_num)).const_mul_left ((1 / 120)))).add ((Dynamics.isBigO_mul_pow (k
    := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k
    := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_r o_u (by norm_num)) o_u
    (by norm_num)) o_u (by norm_num)) o_l0 (by norm_num)).const_mul_left ((1 / 120)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_r o_u (by norm_num)) o_u (by norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)).const_mul_left
    ((1 / 120)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k
    := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k
    := 3) tendsto_norm0 o_r o_u (by norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)) o_l0 (by
    norm_num)).const_mul_left ((1 / 120)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_r o_l0 (by norm_num)) o_l0 (by norm_num)) o_l0
    (by norm_num)) o_l0 (by norm_num)).const_mul_left ((1 / 120)))).congr_left fun y => ?_
  simp only [tv, lowF3]
  ring

@[tmio M, powerlib_domain] private theorem tv_isBigO : (fun y => tv y) =O[𝓝 0] fun y => ‖y‖ :=
  o_u.congr_right fun _ => pow_one _

@[tmio M, powerlib_domain] private theorem tv_tendsto : Tendsto (fun y => tv y) (𝓝 0) (𝓝 0) :=
  tv_isBigO.trans_tendsto tendsto_norm0

/-- **`f₀` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`** (sixth-order Taylor
remainders of `cos`, `sin` and products of pieces of weight at least six). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem f1_sub_low :
    (fun y => f0v y - pv low1L y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hc := Dynamics.isBigO_comp_pow Dynamics.cos_sub_taylor_isBigO tv_tendsto tv_isBigO
  have hn := Dynamics.isBigO_comp_pow Dynamics.sin_sub_taylor5_isBigO tv_tendsto tv_isBigO
  have h1 := Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 hc o_X1 (by norm_num)
  have h2 := Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 hn o_X2 (by norm_num)
  refine (((h1.add h2).const_mul_left (-20)).add split1_isBigO).congr_left fun y => ?_
  simp only [← low1_eq y, f0v]
  ring

/-- **`cos x₀ − 1` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem f2_sub_low :
    (fun y => Real.cos (tv y) - 1 - pv low2L y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hc := Dynamics.isBigO_comp_pow Dynamics.cos_sub_taylor_isBigO tv_tendsto tv_isBigO
  refine (hc.add split2_isBigO).congr_left fun y => ?_
  simp only [← low2_eq y]
  ring

/-- **`sin x₀ − x₀` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem f3_sub_low :
    (fun y => Real.sin (tv y) - tv y - pv low3L y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hn := Dynamics.isBigO_comp_pow Dynamics.sin_sub_taylor5_isBigO tv_tendsto tv_isBigO
  refine (hn.add split3_isBigO).congr_left fun y => ?_
  simp only [← low3_eq y]
  ring

/-! ## The quintic jet of the chart field -/

/-- The jet of the first chart coordinate. -/
def cF : List (ℝ × ℕ × ℕ × ℕ) := cF2 ++ cF3 ++ cF4 ++ cF5

/-- The jet of the second chart coordinate. -/
def cG : List (ℝ × ℕ × ℕ × ℕ) := cG2 ++ cG3 ++ cG4 ++ cG5

/-- The jet of the first chart coordinate from the truncated nonlinearities. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem cF_eq (y : State 2) :
    pv cF y = -13 / 750 * pv low1L y + 1 / 10 * pv low2L y + 1 / 15 * pv low3L y := by
  simp only [pv, cF, cF2, cF3, cF4, cF5, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L,
    low3L4, low3L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The jet of the second chart coordinate from the truncated nonlinearities. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem cG_eq (y : State 2) :
    pv cG y = 13 / 375 * pv low1L y + 13 / 15 * pv low3L y := by
  simp only [pv, cG, cG2, cG3, cG4, cG5, low1L, low1L4, low1L5, low3L,
    low3L4, low3L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- **The first chart coordinate has the jet `cF`**: `G₀ − cF = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G0_sub_jet :
    (fun y => G0 y - pv cF y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((f1_sub_low.const_mul_left (-13 / 750)).add
    (f2_sub_low.const_mul_left (1 / 10))).add
      (f3_sub_low.const_mul_left (1 / 15))).congr_left fun y => ?_
  rw [(G_eq y).1, cF_eq]
  ring

/-- **The second chart coordinate has the jet `cG`**: `G₁ − cG = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G1_sub_jet :
    (fun y => G1 y - pv cG y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine ((f1_sub_low.const_mul_left (13 / 375)).add
    (f3_sub_low.const_mul_left (13 / 15))).congr_left fun y => ?_
  rw [(G_eq y).2, cG_eq]
  ring

/-- The tails of the jet: `G − J₃ = O(‖y‖⁴)` and `G − J₄ = O(‖y‖⁵)` in both coordinates. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_tail_bounds :
    ((fun y => G0 y - pv (cF2 ++ cF3) y) =O[𝓝 0] fun y => ‖y‖ ^ 4) ∧
      ((fun y => G1 y - pv (cG2 ++ cG3) y) =O[𝓝 0] fun y => ‖y‖ ^ 4) ∧
      ((fun y => G0 y - pv (cF2 ++ cF3 ++ cF4) y) =O[𝓝 0] fun y => ‖y‖ ^ 5) ∧
      ((fun y => G1 y - pv (cG2 ++ cG3 ++ cG4) y) =O[𝓝 0] fun y => ‖y‖ ^ 5) := by
  have hF4 : (fun y : State 2 => pv cF4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 := pv_isBigO _ (by simp [cF4])
  have hF5 : (fun y : State 2 => pv cF5 y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := pv_isBigO _ (by simp [cF5])
  have hG4 : (fun y : State 2 => pv cG4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 := pv_isBigO _ (by simp [cG4])
  have hG5 : (fun y : State 2 => pv cG5 y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := pv_isBigO _ (by simp [cG5])
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((mono G0_sub_jet (by norm_num)).add (hF4.add (mono hF5 (by norm_num)))).congr_left
      fun y => ?_
    simp only [cF, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono G1_sub_jet (by norm_num)).add (hG4.add (mono hG5 (by norm_num)))).congr_left
      fun y => ?_
    simp only [cG, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono G0_sub_jet (by norm_num)).add hF5).congr_left fun y => ?_
    simp only [cF, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono G1_sub_jet (by norm_num)).add hG5).congr_left fun y => ?_
    simp only [cG, PlanarFocus.Jet5.poly3_append, pv]; ring

/-! ## The invariance defect -/

/-- The `w`-component of the invariance defect over `y`. -/
def dcomp (y : State 2) : ℝ :=
  dpoly3 hL (y 0) (y 1) 0 (y 1 + G0 y) (-26 * y 0 + G1 y) 0 + 2 * pv hL y -
    (Real.cos (tv y) - 1) + 5 * G0 y

/-- **The homological equations make the polynomial part of the defect of degree at least five**
(`highD` has degrees five to eight). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main_eq_high (y : State 2) :
    dpoly3 hL (y 0) (y 1) 0 (y 1 + pv (cF2 ++ cF3) y) (-26 * y 0 + pv (cG2 ++ cG3) y) 0 +
      2 * pv hL y - pv low2L4 y + 5 * pv (cF2 ++ cF3 ++ cF4) y = pv highD y := by
  simp only [dpoly3_cons, dpoly3_nil, poly3_cons, poly3_nil, hL, hL2, hL3, hL4, cF2, cF3, cF4,
    cG2, cG3, low2L4, highD, pv, List.cons_append, List.nil_append]
  ring

/-- **The invariance defect at a chart point** is `R_{−π/4} (d(y) w)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem defect_eq (y : State 2) :
    invarianceDefect (fderiv ℝ bpt.field 0) (critP (rotC bpt.δ qv) (rotC bpt.δ pv3)) fnl manifold
      (iotaG y) = rotT bpt.δ (dcomp y • wv) := by
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldG y
  have hdef := invarianceDefect_comp_chart (A := fderiv ℝ bpt.field 0) (f := fnl) isChart_G
    hL'.differentiableAt
  rw [show (fun x => manifoldG (piG x)) = manifold from rfl, hL'.fderiv] at hdef
  rw [hdef, chartField_eq, hLv]
  have hφ : manifold (iotaG y) = manifoldG y := by rw [manifold, isChart_G.left_inv]
  have hP : ∀ v, critP (rotC bpt.δ qv) (rotC bpt.δ pv3) v = iotaG (piG v) := fun v =>
    (isChart_G.ι_π v).symm
  have hN : normalField (fderiv ℝ bpt.field 0) (critP (rotC bpt.δ qv) (rotC bpt.δ pv3)) fnl
      manifold (iotaG y) =
      rotT bpt.δ ((-2 * pv hL y + (Real.cos (tv y) - 1 - 5 * G0 y)) • wv) := by
    rw [normalField, iotaG_add_manifold, hφ]
    simp only [_root_.sub_apply, one_apply_eq_self, hP]
    have hA : fderiv ℝ bpt.field 0 (manifoldG y) = rotT bpt.δ ((-2 * pv hL y) • wv) := by
      rw [manifoldG, fderiv_rotT, manifoldH, map_smul, A_wv, smul_smul, pv, mul_comm]
    rw [hA, piG_rotT, map_smul piR, piR_wv, smul_zero, map_zero, sub_zero, fnl_rotT,
      sub_iotaG_piG]
    obtain ⟨c0, -, -⟩ := chartPt_apply y
    rw [frot_apply, c0, ← map_add, add_smul]
    rfl
  rw [hN, ← map_sub, ← sub_smul]
  obtain ⟨r0, r1⟩ := rotR_apply y
  congr 2
  simp only [PiLp.add_apply, r0, r1, dcomp, G0, G1, pv]
  ring

/-- The `w`-component of the defect is `O(‖y‖⁵)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dcomp_isBigO :
    (fun y => dcomp y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := by
  have e : ∀ y, dcomp y = pv highD y +
      (poly3 (hL.map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0 *
          (G0 y - pv (cF2 ++ cF3) y) +
        poly3 (hL.map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0 *
          (G1 y - pv (cG2 ++ cG3) y)) -
      (Real.cos (tv y) - 1 - pv low2L4 y) + 5 * (G0 y - pv (cF2 ++ cF3 ++ cF4) y) := by
    intro y
    rw [← main_eq_high y, dcomp, Dynamics.Degenerate.dpoly3_eq_partials,
      Dynamics.Degenerate.dpoly3_eq_partials]
    ring
  obtain ⟨hG0_3, hG1_3, hG0_4, -⟩ := jet_tail_bounds
  have hdx : (fun y : State 2 => poly3 (hL.map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [hL, hL2, hL3, hL4, Dynamics.Degenerate.dxTerm])
  have hdy : (fun y : State 2 => poly3 (hL.map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [hL, hL2, hL3, hL4, Dynamics.Degenerate.dyTerm])
  have hcos : (fun y : State 2 => Real.cos (tv y) - 1 - pv low2L4 y) =O[𝓝 0]
      fun y => ‖y‖ ^ 5 :=
    ((mono f2_sub_low (by norm_num)).add (pv_isBigO low2L5 (by simp [low2L5]))).congr_left
      fun y => by simp only [low2L, pv, PlanarFocus.Jet5.poly3_append]; ring
  have hhigh : (fun y : State 2 => pv highD y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [highD])
  refine (((hhigh.add ((Dynamics.isBigO_mul_pow tendsto_norm0 hdx hG0_3 (by norm_num)).add
    (Dynamics.isBigO_mul_pow tendsto_norm0 hdy hG1_3 (by norm_num)))).sub hcos).add
      (hG0_4.const_mul_left 5)).congr_left fun y => ?_
  rw [e y]

/-- **The invariance defect is `O(‖u‖⁵)` on the centre subspace.** Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem isOrder_defect :
    IsOrder (critP (rotC bpt.δ qv) (rotC bpt.δ pv3))
      (invarianceDefect (fderiv ℝ bpt.field 0) (critP (rotC bpt.δ qv) (rotC bpt.δ pv3)) fnl
        manifold) 5 := by
  have h := isChart_G.isOrder_of_isBigO (k := 5)
    (G := invarianceDefect (fderiv ℝ bpt.field 0) (critP (rotC bpt.δ qv) (rotC bpt.δ pv3)) fnl
      manifold) ?_
  · exact_mod_cast h
  have h2 : (fun y : State 2 => rotT bpt.δ (dcomp y • wv)) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (IsBigO.of_bound (‖rotT bpt.δ‖ * ‖wv‖) (Eventually.of_forall fun y => by
      calc ‖rotT bpt.δ (dcomp y • wv)‖ ≤ ‖rotT bpt.δ‖ * ‖dcomp y • wv‖ :=
            (rotT bpt.δ).le_opNorm _
        _ = ‖rotT bpt.δ‖ * ‖wv‖ * ‖dcomp y‖ := by rw [norm_smul]; ring)).trans dcomp_isBigO
  exact h2.congr_left fun y => (defect_eq y).symm

/-! ## The jet in the rotation frame and the second Lyapunov coefficient -/

/-- The normalised jet `J/ω` (`τ = ωt`, `ω = √26`). -/
def jetN : Jet5 where
  a20 := (0)
  a11 := (-52 / 75)
  a02 := (37 / 75 * r)
  b20 := (0)
  b11 := (-4 / 75 * r)
  b02 := (104 / 75)
  a30 := (-101062 / 50625 * r)
  a21 := (1111682 / 50625)
  a12 := (-348218 / 50625 * r)
  a03 := (38584 / 1875)
  b30 := (-202124 / 50625)
  b21 := (202124 / 50625 * r)
  b12 := (-929656 / 50625)
  b03 := (43732 / 16875 * r)
  a40 := (-230447313161 / 8132906250 * r)
  a31 := (-2324322798122 / 4066453125)
  a22 := (-3196703107 / 1355484375 * r)
  a13 := (-96291298324 / 162658125)
  a04 := (-118816150414 / 4066453125 * r)
  b40 := (120151671484 / 4066453125)
  b31 := (-355988944064 / 4066453125 * r)
  b22 := (-102633672284 / 1355484375)
  b13 := (-10596288196 / 162658125 * r)
  b04 := (-1169111828768 / 4066453125)
  a50 := (24569230470733 / 304983984375 * r)
  a41 := (947128354866083 / 60996796875)
  a32 := (-70868351092682 / 60996796875 * r)
  a23 := (1314388778008358 / 60996796875)
  a14 := (-901107511252 / 1742765625 * r)
  a05 := (236572686022946 / 43569140625)
  b50 := (-642892440121594 / 304983984375)
  b41 := (80796516389186 / 60996796875 * r)
  b32 := (-14463979405564 / 60996796875)
  b23 := (49288451076176 / 60996796875 * r)
  b14 := (51021131947084 / 12199359375)
  b05 := (-45125420550496 / 304983984375 * r)

/-- The quintic jet of the chart field in the rotation coordinates of `rotR`. -/
def jet : Jet5 where
  a20 := r * (0)
  a11 := r * (-52 / 75)
  a02 := r * (37 / 75 * r)
  b20 := r * (0)
  b11 := r * (-4 / 75 * r)
  b02 := r * (104 / 75)
  a30 := r * (-101062 / 50625 * r)
  a21 := r * (1111682 / 50625)
  a12 := r * (-348218 / 50625 * r)
  a03 := r * (38584 / 1875)
  b30 := r * (-202124 / 50625)
  b21 := r * (202124 / 50625 * r)
  b12 := r * (-929656 / 50625)
  b03 := r * (43732 / 16875 * r)
  a40 := r * (-230447313161 / 8132906250 * r)
  a31 := r * (-2324322798122 / 4066453125)
  a22 := r * (-3196703107 / 1355484375 * r)
  a13 := r * (-96291298324 / 162658125)
  a04 := r * (-118816150414 / 4066453125 * r)
  b40 := r * (120151671484 / 4066453125)
  b31 := r * (-355988944064 / 4066453125 * r)
  b22 := r * (-102633672284 / 1355484375)
  b13 := r * (-10596288196 / 162658125 * r)
  b04 := r * (-1169111828768 / 4066453125)
  a50 := r * (24569230470733 / 304983984375 * r)
  a41 := r * (947128354866083 / 60996796875)
  a32 := r * (-70868351092682 / 60996796875 * r)
  a23 := r * (1314388778008358 / 60996796875)
  a14 := r * (-901107511252 / 1742765625 * r)
  a05 := r * (236572686022946 / 43569140625)
  b50 := r * (-642892440121594 / 304983984375)
  b41 := r * (80796516389186 / 60996796875 * r)
  b32 := r * (-14463979405564 / 60996796875)
  b23 := r * (49288451076176 / 60996796875 * r)
  b14 := r * (51021131947084 / 12199359375)
  b05 := r * (-45125420550496 / 304983984375 * r)

/-- The second rotation coordinate of `rotR`, `−y₁/√26`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem frameY_rotR (u : State 2) :
    frameY rotR r u = -r⁻¹ * u 1 := by
  rw [PlanarFocus.frameY_apply, (rotR_apply u).1]

/-- The jet in the rotation frame is the chart jet: `F_J(a, Y) = cF(a, −√26 Y)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem jetF_frame (a Y : ℝ) :
    poly3 jet.F a Y 0 = poly3 cF a (-(r * Y)) 0 := by
  simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4,
    PlanarFocus.Jet5.F5, jet, cF, cF2, cF3, cF4, cF5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  linear_combination (24569230470733*a ^ 5/304983984375 - 230447313161*a ^ 4/8132906250 - 101062*a ^
    3/50625 - 50553414538783*a ^ 2*Y ^ 3*r/60996796875 + 34657981202*a*Y ^ 4*r ^ 2/1742765625 +
    3703511474*a*Y ^ 3*r/162658125 - 699919189417*Y ^ 5*r ^ 3/87138281250 - 9098949462421*Y ^
    5*r/43569140625 + 4569851939*Y ^ 4*r ^ 2/4066453125 - 1484*Y ^ 3*r/1875) * r_sq

/-- The jet in the rotation frame is the chart jet: `√26 G_J(a, Y) = −cG(a, −√26 Y)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem jetG_frame (a Y : ℝ) :
    r * poly3 jet.G a Y 0 = -poly3 cG a (-(r * Y)) 0 := by
  simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet.G2, PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4,
    PlanarFocus.Jet5.G5, jet, cG, cG2, cG3, cG4, cG5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  linear_combination (-642892440121594*a ^ 5/304983984375 + 80796516389186*a ^ 4*Y*r/60996796875 +
    120151671484*a ^ 4/4066453125 - 355988944064*a ^ 3*Y*r/4066453125 - 202124*a ^ 3/50625 +
    202124*a ^ 2*Y*r/50625 - 1962351228734*a*Y ^ 4*r ^ 2/12199359375 - 4*a*Y*r/75 + 1735593098096*Y
    ^ 5*r ^ 3/304983984375 + 44965839568*Y ^ 4*r ^ 2/4066453125) * r_sq

/-- The normalised jet (`τ = √26 t`): `J/√26 = jetN`. -/
@[tmio M, powerlib_domain] theorem jet_nrm : jet.nrm r = jetN := by
  have h : r ≠ 0 := r_pos.ne'
  simp only [PlanarFocus.Jet5.nrm, jet, jetN, mul_div_cancel_left₀ _ h]

/-- The Lyapunov chain of the normalised jet: `c30` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c30 : jetN.c30 1 = (104 / 75) := by
  simp only [PlanarFocus.Jet.c30]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c21` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c21 : jetN.c21 1 = (0) := by
  simp only [PlanarFocus.Jet.c21]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c12` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c12 : jetN.c12 1 = (208 / 75) := by
  simp only [PlanarFocus.Jet.c12]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c03` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c03 : jetN.c03 1 = (-22 / 75 * r) := by
  simp only [PlanarFocus.Jet.c03]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `d40` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d40 : jetN.d40 1 = (562783 / 50625) := by
  simp only [PlanarFocus.Jet.d40]
  simp only [jetN]
  linear_combination (22/1875) * r_sq

/-- The Lyapunov chain of the normalised jet: `d31` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d31 : jetN.d31 1 = (202124 / 50625 * r) := by
  simp only [PlanarFocus.Jet.d31]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `d22` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d22 : jetN.d22 1 = (289016 / 50625) := by
  simp only [PlanarFocus.Jet.d22]
  simp only [jetN]
  linear_combination (44/1875) * r_sq

/-- The Lyapunov chain of the normalised jet: `d13` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d13 : jetN.d13 1 = (17992 / 3375 * r) := by
  simp only [PlanarFocus.Jet.d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `l1` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l1 : jetN.l1 1 = (0) := by
  simp only [PlanarFocus.Jet.l1]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r50 : jetN.r50 1 = (-52843476517 / 813290625 * r) := by
  simp only [PlanarFocus.Jet5.r50]
  rw [jv_c30, jv_c21, jv_d40, jv_d31]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r41 : jetN.r41 1 = (-4274808431036 / 4066453125) := by
  simp only [PlanarFocus.Jet5.r41]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22]
  simp only [jetN]
  linear_combination (-808496/3796875) * r_sq

/-- The Lyapunov chain of the normalised jet: `r32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r32 : jetN.r32 1 = (-98602249018 / 580921875 * r) := by
  simp only [PlanarFocus.Jet5.r32]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r23 : jetN.r23 1 = (-5053519791944 / 4066453125) := by
  simp only [PlanarFocus.Jet5.r23]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (130156/84375) * r_sq

/-- The Lyapunov chain of the normalised jet: `r14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r14 : jetN.r14 1 = (-622795874116 / 4066453125 * r) := by
  simp only [PlanarFocus.Jet5.r14]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r05 : jetN.r05 1 = (-2069209911808 / 4066453125) := by
  simp only [PlanarFocus.Jet5.r05]
  rw [jv_c12, jv_c03, jv_d13]
  simp only [jetN]
  linear_combination (442208/1265625) * r_sq

/-- The Lyapunov chain of the normalised jet: `e50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e50 : jetN.e50 1 = (-2632342944764 / 4066453125) := by
  simp only [PlanarFocus.Jet5.e50]
  rw [jv_r41, jv_r23, jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e41 : jetN.e41 1 = (52843476517 / 813290625 * r) := by
  simp only [PlanarFocus.Jet5.e41]
  rw [jv_r50]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e32 : jetN.e32 1 = (-4443453146392 / 4066453125) := by
  simp only [PlanarFocus.Jet5.e32]
  rw [jv_r23, jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e23 : jetN.e23 1 = (582361757822 / 4066453125 * r) := by
  simp only [PlanarFocus.Jet5.e23]
  rw [jv_r50, jv_r32]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e14 : jetN.e14 1 = (-2069209911808 / 4066453125) := by
  simp only [PlanarFocus.Jet5.e14]
  rw [jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e05 : jetN.e05 1 = (357503877952 / 4066453125 * r) := by
  simp only [PlanarFocus.Jet5.e05]
  rw [jv_r50, jv_r32, jv_r14]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r60 : jetN.r60 1 = (-3749184705058 / 60996796875 * r) := by
  simp only [PlanarFocus.Jet5.r60]
  rw [jv_c30, jv_c21, jv_d40, jv_d31, jv_e50, jv_e41]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r51 : jetN.r51 1 = (310663764577582 / 11295703125) := by
  simp only [PlanarFocus.Jet5.r51]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22, jv_e50, jv_e41, jv_e32]
  simp only [jetN]
  linear_combination (-387521017468/33887109375) * r_sq

/-- The Lyapunov chain of the normalised jet: `r42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r42 : jetN.r42 1 = (-610561280694716 / 304983984375 * r) := by
  simp only [PlanarFocus.Jet5.r42]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e50, jv_e41, jv_e32,
    jv_e23]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r33 : jetN.r33 1 = (12993741014356492 / 304983984375) := by
  simp only [PlanarFocus.Jet5.r33]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e41, jv_e32, jv_e23,
    jv_e14]
  simp only [jetN]
  linear_combination (49868313919892/304983984375) * r_sq

/-- The Lyapunov chain of the normalised jet: `r24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r24 : jetN.r24 1 = (-94685410542008 / 101661328125 * r) := by
  simp only [PlanarFocus.Jet5.r24]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13, jv_e32, jv_e23, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r15 : jetN.r15 1 = (5621502490102876 / 304983984375) := by
  simp only [PlanarFocus.Jet5.r15]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13, jv_e23, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (54885658259588/304983984375) * r_sq

/-- The Lyapunov chain of the normalised jet: `r06` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r06 : jetN.r06 1 = (1666589833376 / 4841015625 * r) := by
  simp only [PlanarFocus.Jet5.r06]
  rw [jv_c12, jv_c03, jv_d13, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f60 : jetN.f60 1 = (3417715773479306 / 304983984375) := by
  simp only [PlanarFocus.Jet5.f60]
  rw [jv_r51, jv_r33, jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f51 : jetN.f51 1 = (-2334807943273 / 69710625000 * r) := by
  simp only [PlanarFocus.Jet5.f51]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f42 : jetN.f42 1 = (2019728832880187 / 101661328125) := by
  simp only [PlanarFocus.Jet5.f42]
  rw [jv_r33, jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f33 : jetN.f33 1 = (157535077368097 / 304983984375 * r) := by
  simp only [PlanarFocus.Jet5.f33]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f24 : jetN.f24 1 = (2810751245051438 / 304983984375) := by
  simp only [PlanarFocus.Jet5.f24]
  rw [jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f15 : jetN.f15 1 = (7004228380643 / 15946875000 * r) := by
  simp only [PlanarFocus.Jet5.f15]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `k6` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_k6 : jetN.k6 1 = (-1525502329 / 16065000 * r) := by
  simp only [PlanarFocus.Jet5.k6]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `l2` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l2 : jetN.l2 1 = (-1525502329 / 8032500 * r) := by
  simp only [PlanarFocus.Jet5.l2]
  rw [jv_k6]
  linear_combination (0) * r_sq

/-- `l₁(J) = 0` at the degenerate point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1_eq_zero : jet.l1 r = 0 := by
  rw [← PlanarFocus.Jet5.l1_nrm jet r r_pos.ne', jet_nrm, jv_l1]

/-- **`l₂(J) = −1525502329√26/8032500 < 0` at the degenerate point.** Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem jet_l2_eq : jet.l2 r = -1525502329 / 8032500 * r := by
  rw [← PlanarFocus.Jet5.l2_nrm jet r r_pos.ne', jet_nrm, jv_l2]

end BautinStable

open BautinStable in
/-- **A locally asymptotically stable Bautin point of power synchronization**: at `E = R = L = 1`,
`ω₀ = 5`, `V = 5√2/4`, `K_p = 52/5`, `P_ref = −1/4`, `δ* = −π/4` (`ℓ₁ = 0`,
`Line.PSC.BautinStable.bpt_firstLyapunov`) the model is a weak focus of the second order with
`l₂ = −1525502329√26/8032500 < 0` (a supercritical Bautin point), read in the chart
`ι = R_{−π/4} ι'`, `π = π' R_{π/4}` of the critical plane (the approximate centre manifold
`BautinStable.manifold`, invariance defect `O(‖u‖⁵)`, the quintic jet `BautinStable.jet`;
`mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`). -/
@[tmio TM, powerlib_domain] theorem stable_bautin_mem_den_locallyAsymptoticallyStable :
    connection% (BautinStable.bpt ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨h2, h1, h0⟩ := bpt_coeffs
  have hr0 : r ≠ 0 := r_pos.ne'
  refine mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg bpt (by rw [h1]; norm_num)
    (by rw [h0]; norm_num) (by rw [h2, h1, h0]; norm_num) isCriticalPair_bpt isChart_G
    rotR_rotR ⟨contDiffAt_manifold, manifold_zero, fderiv_manifold_zero, critP_manifold⟩
    isOrder_defect (J := jet) ⟨?_, ?_⟩
    ⟨jet_l1_eq_zero, by rw [jet_l2_eq]; nlinarith [r_pos]⟩
  · refine (G0_sub_jet.trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => bpt.field x - fderiv ℝ bpt.field 0 x) = fnl from rfl, chartField_eq,
      frameY_rotR, jetF_frame, show -(r * (-r⁻¹ * y 1)) = y 1 by field_simp]
    simp only [PlanarFocus.frameX_apply, PiLp.add_apply, (rotR_apply y).1, G0, Bautin.pv]
    field_simp
    ring
  · refine ((G1_sub_jet.const_mul_left (-r⁻¹)).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    have hG := jetG_frame (y 0) (-r⁻¹ * y 1)
    rw [show -(r * (-r⁻¹ * y 1)) = y 1 by field_simp] at hG
    have hG' : poly3 jet.G (y 0) (-r⁻¹ * y 1) 0 = -r⁻¹ * poly3 cG (y 0) (y 1) 0 := by
      have e : poly3 cG (y 0) (y 1) 0 = -(r * poly3 jet.G (y 0) (-r⁻¹ * y 1) 0) := by linarith
      rw [e]; field_simp
    rw [show (fun x => bpt.field x - fderiv ℝ bpt.field 0 x) = fnl from rfl, chartField_eq,
      frameY_rotR, frameY_rotR, PlanarFocus.frameX_apply, hG']
    simp only [PiLp.add_apply, (rotR_apply y).2, G1, Bautin.pv]
    have h26 : (26 : ℝ) = r ^ 2 := r_sq.symm
    field_simp
    rw [h26]
    ring

end PSC
end powerlib.GFM.Line
