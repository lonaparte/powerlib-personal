import theorem.GridTiedConverter.GFM.HopfBautinPSC

/-! # The second Bautin point of the power-synchronization angle path is unstable

Domain module.

Model boundary.
* The three-state power-synchronization law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged (state `(δ, i_d, i_q)`, grid dq
  frame, export-positive power, `δ̇ = K_p (P_ref − P_e)`, `L i̇ = E e^{jδ} − V − (R + jX) i`), read
  about a selected angle (`Line.PSC.Model`) on `Line.PSC.family`. Excluded as there.
* The rotated frame, for every balanced physical model at every angle: the rotation `rotT θ` of
  the current components (the real counterpart of `Line.PSC.rotC`); the translated field in the
  frame rotated with the operating angle, `F(R_{δ*} z) = R_{δ*} F_rot(z)`,
  `F_rot = (N(1 − cos z₀) + κ sin z₀ − G(cos z₀ z₁ + sin z₀ z₂), b(cos z₀ − 1) − σ z₁ + ω₀ z₂,
  b sin z₀ − ω₀ z₁ − σ z₂)` (`N = K_p P_ref`, `κ = K_p Q`, `G = K_p E`, `b = E/L`, `σ = R/L`), its
  linear part `J_rot` and the critical projection of a rotated pair.
* The Bautin form along an angle path (`κ = K_p Q`, `σ = R/L`, `ω₀` fixed, the angle term `t`
  varying): `𝔅_P = 𝔊_P (t − a₁)² + a₁² ((κ − σ)² + ω₀²) 𝔆_P` with the cubic `𝔆_P`
  (`Line.PSC.bautinC`); an angle path carries no Bautin point when `𝔊_P` and `𝔆_P` have the same
  strict sign, and the two points `t = a₁ (1 ± √(−((κ − σ)² + ω₀²) 𝔆_P/𝔊_P))` when the signs
  are opposite.
* The point: on the unit line `E = R = L = ω₀ = 1` the angle path with the linear data of the
  first Bautin point (`κ = −2`, `K_p = 20`, `a₂ = 4`, `a₁ = 6`, `a₀ = 24`) has the Bautin form
  `𝔅_P = 𝔊_P t (t − 12)`; its second zero `t = 12` is the model `BautinAngle.bpt`: `V = 3√2/5`,
  `K_p = 20`, `P_ref = 1/2`, `δ* = π/4`, operating current `(√2/5, 3√2/10)`. In the frame rotated
  by `π/4` its field is that of the first point `Line.PSC.Bautin.bpt` (`unitLine (6/5) 20`) with
  the same linear part `A = [[−2, −20, 0], [0, −1, 1], [1, −1, −1]]` and the nonlinearities
  `f_rot = (−10(cos z₀ − 1) − 20((cos z₀ − 1) z₁ + sin z₀ z₂) − 2(sin z₀ − z₀), cos z₀ − 1,
  sin z₀ − z₀)` (`N = 10` in place of `−2`).
* The chart: `ι = R_{π/4} ι'`, `π = π' R_{−π/4}`, `ι'`, `π'` the rational chart of the first point
  (`Bautin.iotaR`, `Bautin.piR`, reduced linear part `Bautin.rotR y = (y₁, −6 y₀)`), a chart of the
  critical plane of the critical pair `(R_{π/4} q, R_{π/4} p)` at `ω = √6`. The approximate centre
  manifold is `φ = R_{π/4} H ∘ π`, `H(y) = h(y) w`, `w = (10, 1, −3)`, `h` of degrees two to four
  with rational coefficients.
* Level: exact. The trigonometric nonlinearities enter through the sixth-order Taylor remainders
  of `cos` and `sin`; the rotation is exact (`cos² + sin² = 1`, `cos(π/4) = sin(π/4) = √2/2`);
  the homological identities of degrees two to four and every chart identity are rational;
  `l₁ = 0` and `l₂ = 34000√6/77` are computed in `ℚ(√6)`. No floating point, sampling or search.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3 (Bautin points, the
second Lyapunov coefficient); Carr, *Applications of Centre Manifold Theory* (1981), §2.4–2.5. The
completed Bautin form was found by factorising `𝔊_P − a₂ ℌ_P` with SymPy (untrusted) and is
checked by `ring`. The family law is `Line.PSC.mem_den_unstable_of_secondLyapunov_pos`
(`theorem/GridTiedConverter/GFM/HopfBautinPSC.lean`, generic laws
`theorem/Dynamics/CenterReductionBautin.lean`), read in the chart `ι`, `π` (any chart of the
critical plane is admitted); the critical pair is `Line.PSC.Model.isCriticalPair_crit`
(`theorem/GridTiedConverter/GFM/HopfLinePSC.lean`, the rotated frame of `Model.critQ`,
`Model.critP`), the degeneracy `ℓ₁ = 0` is `Line.PSC.Model.sign_firstLyapunov_crit` with
`𝔅_P(−2, 1, 1, 12) = 0`. The centre manifold, the jet and the Lyapunov chain were derived with
SymPy in exact rational and `ℚ(√6)` arithmetic (untrusted, discovery evidence only); every identity
is checked here.

Results.
* The rotated frame: `Line.PSC.rotT`, `Line.PSC.rotT_apply`, `Line.PSC.rotT_neg_rotT`,
  `Line.PSC.rotT_rotT_neg`, `Line.PSC.critP_rotC` (`P(R q, R p) = R P(q, p) R⁻¹`),
  `Line.PSC.Model.rotField`, **`Line.PSC.Model.field_rotT`**, `Line.PSC.Model.rotJ`,
  `Line.PSC.Model.fderiv_field_rotT`.
* The Bautin form along an angle path: `Line.PSC.bautinC`, **`Line.PSC.bautinForm_eq_cubic`**,
  `Line.PSC.bautinForm_neg_of_cubic`, `Line.PSC.bautinForm_pos_of_cubic`.
* The point: `BautinAngle.bpt`, `BautinAngle.bpt_trig`, `BautinAngle.bpt_physical`,
  `BautinAngle.bpt_balanced`, `BautinAngle.bpt_Q` (`Q = −1/10`), `BautinAngle.bpt_coeffs`,
  `BautinAngle.bpt_angleShift` (`t = 12`), **`BautinAngle.bpt_firstLyapunov`** (a critical pair at
  `ω = √6` exists and every critical pair has `ℓ₁ = 0`).
* The rotated field at the point: `BautinAngle.rotJ_bpt`, `BautinAngle.fderiv_rotT`,
  `BautinAngle.frot`, `BautinAngle.frot_apply`, `BautinAngle.fnl`, `BautinAngle.fnl_rotT`; the
  critical pair `BautinAngle.critQ_eq`, `BautinAngle.critP_eq`, `BautinAngle.isCriticalPair_bpt`;
  the chart `BautinAngle.iotaG`, `BautinAngle.piG`, `BautinAngle.piG_rotT`,
  **`BautinAngle.isChart_G`**, `BautinAngle.sub_iotaG_piG`.
* The manifold: `BautinAngle.hL2` … `BautinAngle.hL4`, `BautinAngle.hL`, `BautinAngle.manifoldH`,
  `BautinAngle.manifoldG`, `BautinAngle.manifold`, `BautinAngle.piR_manifoldH`,
  `BautinAngle.hasFDerivAt_manifoldH`, `BautinAngle.hasFDerivAt_manifoldG`,
  `BautinAngle.contDiffAt_manifold`, `BautinAngle.manifold_zero`,
  `BautinAngle.fderiv_manifold_zero`, `BautinAngle.critP_manifold`.
* The chart field and its quintic jet: `BautinAngle.chartPt`, `BautinAngle.iotaG_add_manifold`,
  `BautinAngle.chartField_eq`, `BautinAngle.chartPt_apply`, `BautinAngle.G0`, `BautinAngle.G1`,
  `BautinAngle.f0v`, `BautinAngle.G_eq`; `BautinAngle.low1_eq` … `BautinAngle.low3_eq`,
  `BautinAngle.split1_isBigO` … `BautinAngle.split3_isBigO`, `BautinAngle.f1_sub_low` …
  `BautinAngle.f3_sub_low`, `BautinAngle.cF`, `BautinAngle.cG`, `BautinAngle.cF_eq`,
  `BautinAngle.cG_eq`, `BautinAngle.G0_sub_jet`, `BautinAngle.G1_sub_jet`,
  `BautinAngle.jet_tail_bounds`.
* **The invariance defect is `O(‖u‖⁵)`**: `BautinAngle.dcomp`, `BautinAngle.main_eq_high`,
  `BautinAngle.defect_eq`, `BautinAngle.dcomp_isBigO`, `BautinAngle.isOrder_defect`.
* The jet in the rotation frame: `BautinAngle.jet`, `BautinAngle.jetN`, `BautinAngle.jetF_frame`,
  `BautinAngle.jetG_frame`, `BautinAngle.jet_nrm`; the Lyapunov chain `BautinAngle.jv_c30` …
  `BautinAngle.jv_l2`; **`BautinAngle.jet_l1_eq_zero`** and **`BautinAngle.jet_l2_eq`**
  (`l₂(J) = 34000√6/77 > 0`).

Family and connection conclusions.
No new family: connection conclusions on `Line.PSC.family`.
* `Line.PSC.mem_den_unstable_of_bautinG_neg_of_bautinC_neg` and
  `Line.PSC.mem_den_locallyAsymptoticallyStable_of_bautinG_pos_of_bautinC_pos`: a balanced
  physical model on the Hopf boundary whose linear data have `𝔊_P, 𝔆_P < 0` (`> 0`) is unstable
  (locally asymptotically stable) at every angle.
* **`Line.PSC.angle_bautin_mem_den_unstable`**: the second Bautin point of the angle path
  (`V = 3√2/5`, `K_p = 20`, `P_ref = 1/2`, `δ* = π/4`) is unstable (a weak focus of the second
  order, `l₂ > 0`). Both zeros `t = 0` (`Line.PSC.unitLine_bautin_mem_den_unstable`) and `t = 12`
  of the Bautin form on this angle path are therefore unstable; the other points of the path
  (`𝔅_P ≠ 0`) are decided by `ℓ₁` (`Line.PSC.mem_den_locallyAsymptoticallyStable_of_bautinForm_pos`,
  `Line.PSC.mem_den_unstable_of_bautinForm_neg`).
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

/-! ## The frame rotated with the operating angle -/

/-- **The rotation of the current components by `θ`**,
`(z₀, z₁, z₂) ↦ (z₀, cos θ z₁ − sin θ z₂, sin θ z₁ + cos θ z₂)`: the grid-frame reading of a state
of the frame rotated by `θ` (the real counterpart of `Line.PSC.rotC`). -/
def rotT (θ : ℝ) : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
    !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ]

/-- The rotation, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotT_apply (θ : ℝ) (z : State 3) (i : Fin 3) :
    rotT θ z i = ![z 0, Real.cos θ * z 1 - Real.sin θ * z 2,
      Real.sin θ * z 1 + Real.cos θ * z 2] i := by
  rw [rotT, Dynamics.toEuclideanCLM_apply3]
  fin_cases i <;> simp
  ring

/-- `rotT (−θ)` inverts `rotT θ`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotT_neg_rotT (θ : ℝ) (z : State 3) :
    rotT (-θ) (rotT θ z) = z := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i
  fin_cases i <;> simp [rotT_apply, Real.cos_neg, Real.sin_neg]
  · linear_combination (z 1) * h
  · linear_combination (z 2) * h

/-- `rotT θ` inverts `rotT (−θ)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotT_rotT_neg (θ : ℝ) (z : State 3) :
    rotT θ (rotT (-θ) z) = z := by
  simpa using rotT_neg_rotT (-θ) z

/-- **The critical projection of a rotated pair**: `P(rotC θ q, rotC θ p) = R_θ P(q, p) R_{−θ}`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critP_rotC (θ : ℝ) (q p : Fin 3 → ℂ) (x : State 3) :
    critP (rotC θ q) (rotC θ p) x = rotT θ (critP q p (rotT (-θ) x)) := by
  have hπ : critπ (rotC θ p) x = critπ p (rotT (-θ) x) := by
    ext j
    fin_cases j <;>
      simp [critπ_apply0, critπ_apply1, reV_apply, imV_apply, PiLp.inner_apply,
        Fin.sum_univ_three, rotC, rotT_apply, Real.cos_neg, Real.sin_neg, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im] <;> ring
  rw [critP, ContinuousLinearMap.comp_apply, hπ, critP, ContinuousLinearMap.comp_apply]
  ext i
  fin_cases i <;> simp [critι_apply, reV_apply, imV_apply, rotC, rotT_apply,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]

/-- **The field in the frame rotated with the operating angle**: with `N = K_p P_ref`,
`κ = K_p Q`, `G = K_p E`, `b = E/L`, `σ = R/L`, `w = ω₀`,
`(N(1 − cos z₀) + κ sin z₀ − G(cos z₀ z₁ + sin z₀ z₂), b(cos z₀ − 1) − σ z₁ + w z₂,
b sin z₀ − w z₁ − σ z₂)`. -/
def Model.rotField (m : Model) (z : State 3) : State 3 :=
  WithLp.toLp 2 ![m.g.Kp * m.g.Pref * (1 - Real.cos (z 0)) + m.g.Kp * m.Q * Real.sin (z 0) -
      m.g.Kp * m.g.E * (Real.cos (z 0) * z 1 + Real.sin (z 0) * z 2),
    m.g.E / m.g.L * (Real.cos (z 0) - 1) - m.g.R / m.g.L * z 1 + m.g.ω0 * z 2,
    m.g.E / m.g.L * Real.sin (z 0) - m.g.ω0 * z 1 - m.g.R / m.g.L * z 2]

/-- **The translated field in the rotated frame**: for a balanced physical model,
`F(R_{δ*} z) = R_{δ*} F_rot(z)` (`Model.rotField`); the nonlinear counterpart of the rotated
derivatives of `theorem/GridTiedConverter/GFM/HopfLinePSC.lean`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.field_rotT {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) (z : State 3) : m.field (rotT m.δ z) = rotT m.δ (m.rotField z) := by
  have hL : m.g.L ≠ 0 := hp.1.L.ne'
  have hZ : m.g.absSq ≠ 0 := hp.1.absSq_pos.ne'
  obtain ⟨hd, hq⟩ :=
    (m.g.rate_eq_zero_iff hL hZ m.δ (m.g.is m.δ).re (m.g.is m.δ).im).mpr ⟨rfl, rfl⟩
  have hP : m.g.qssPower m.δ = m.g.Pref := hb
  have hcs := Real.sin_sq_add_cos_sq m.δ
  simp only [Network.qssPower, Network.power_eq] at hP
  simp only [Network.rateD, Network.rateQ, Network.X, div_eq_zero_iff, hL, or_false] at hd hq
  ext i
  fin_cases i
  · simp [Model.field, PSC.field, Model.point, qss, rotT_apply, Model.rotField,
      Network.power_eq, Real.cos_add, Real.sin_add, Model.Q, Network.qssReactive,
      Network.reactive_eq]
    linear_combination (-(m.g.Kp * Real.cos (z 0))) * hP -
      m.g.Kp * m.g.E * (Real.cos (z 0) * z 1 + Real.sin (z 0) * z 2) * hcs
  · simp [Model.field, PSC.field, Model.point, qss, rotT_apply, Model.rotField,
      Network.rateD, Real.cos_add, Network.X]
    field_simp
    linear_combination hd
  · simp [Model.field, PSC.field, Model.point, qss, rotT_apply, Model.rotField,
      Network.rateQ, Real.sin_add, Network.X]
    field_simp
    linear_combination hq

/-- The Jacobian of the rotated frame, `[[κ, −G, 0], [0, −σ, w], [b, −w, −σ]]`. -/
def Model.rotJ (m : Model) : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
    !![m.g.Kp * m.Q, -(m.g.Kp * m.g.E), 0; 0, -(m.g.R / m.g.L), m.g.ω0;
      m.g.E / m.g.L, -m.g.ω0, -(m.g.R / m.g.L)]

/-- **The linear part in the rotated frame**: `DF(0) R_{δ*} = R_{δ*} J_rot`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Model.fderiv_field_rotT (m : Model) (hL : m.g.L ≠ 0)
    (z : State 3) : fderiv ℝ m.field 0 (rotT m.δ z) = rotT m.δ (m.rotJ z) := by
  rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
    zero_add, Model.fderiv_point, m.jac_eq hL]
  have hcs := Real.sin_sq_add_cos_sq m.δ
  ext i
  fin_cases i <;> simp [Model.rotJ, rotT_apply, Dynamics.toEuclideanCLM_apply3]
  · linear_combination (-(m.g.Kp * m.g.E * z 1)) * hcs
  · ring
  · ring


/-! ## The Bautin form along an angle path -/

/-- The cubic `𝔆_P(κ, σ, w) = 4κ³ + 5κ²σ − 19κσ² − 11κw² + 10σ³ + 14σw²`: by
`𝔊_P − a₂ ℌ_P = −((κ − σ)² + w²) 𝔆_P` it carries the discriminant of the PSC Bautin form in the
angle term (`Line.PSC.bautinForm_eq_cubic`). -/
def bautinC (κ σ w : ℝ) : ℝ :=
  4 * κ ^ 3 + 5 * κ ^ 2 * σ - 19 * κ * σ ^ 2 - 11 * κ * w ^ 2 + 10 * σ ^ 3 + 14 * σ * w ^ 2

/-- **The Bautin form completed in the angle term**: with `a₁ = σ² + w² − 2σκ`,
`𝔅_P(κ, σ, w, t) = 𝔊_P (t − a₁)² + a₁² ((κ − σ)² + w²) 𝔆_P`. On an angle path (`κ`, `σ`, `w`
fixed, `t` varying) the Bautin points are the real roots
`t = a₁ (1 ± √(−((κ − σ)² + w²) 𝔆_P/𝔊_P))`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_eq_cubic (κ σ w t : ℝ) :
    bautinForm κ σ w t = bautinG κ σ w * (t - (σ ^ 2 + w ^ 2 - 2 * σ * κ)) ^ 2 +
      (σ ^ 2 + w ^ 2 - 2 * σ * κ) ^ 2 * ((κ - σ) ^ 2 + w ^ 2) * bautinC κ σ w := by
  unfold bautinForm bautinG bautinH bautinC
  ring

/-- **No Bautin point on a subcritical angle path**: `𝔊_P < 0` and `𝔆_P < 0` give `𝔅_P < 0` at
every angle term (`a₁ ≠ 0`, `w > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_neg_of_cubic {κ σ w : ℝ} (t : ℝ)
    (h1 : σ ^ 2 + w ^ 2 - 2 * σ * κ ≠ 0) (hw : 0 < w) (hG : bautinG κ σ w < 0)
    (hC : bautinC κ σ w < 0) : bautinForm κ σ w t < 0 := by
  rw [bautinForm_eq_cubic]
  have hQ : 0 < (κ - σ) ^ 2 + w ^ 2 := by positivity
  have ha : 0 < (σ ^ 2 + w ^ 2 - 2 * σ * κ) ^ 2 := by positivity
  nlinarith [mul_nonneg (neg_nonneg.mpr hG.le) (sq_nonneg (t - (σ ^ 2 + w ^ 2 - 2 * σ * κ))),
    mul_pos (mul_pos ha hQ) (neg_pos.mpr hC)]

/-- **No Bautin point on a supercritical angle path**: `𝔊_P > 0` and `𝔆_P > 0` give `𝔅_P > 0` at
every angle term (`a₁ ≠ 0`, `w > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinForm_pos_of_cubic {κ σ w : ℝ} (t : ℝ)
    (h1 : σ ^ 2 + w ^ 2 - 2 * σ * κ ≠ 0) (hw : 0 < w) (hG : 0 < bautinG κ σ w)
    (hC : 0 < bautinC κ σ w) : 0 < bautinForm κ σ w t := by
  rw [bautinForm_eq_cubic]
  have hQ : 0 < (κ - σ) ^ 2 + w ^ 2 := by positivity
  have ha : 0 < (σ ^ 2 + w ^ 2 - 2 * σ * κ) ^ 2 := by positivity
  nlinarith [mul_nonneg hG.le (sq_nonneg (t - (σ ^ 2 + w ^ 2 - 2 * σ * κ))),
    mul_pos (mul_pos ha hQ) hC]

/-- **A subcritical angle path**: a balanced physical model on the Hopf boundary
(`a₁, a₀ > 0`, `a₂ a₁ = a₀`) with `𝔊_P < 0` and `𝔆_P < 0` at its `(K_p Q, R/L, ω₀)` is unstable,
whatever its angle (`Line.PSC.mem_den_unstable_of_bautinForm_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bautinG_neg_of_bautinC_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hG : bautinG (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 < 0)
    (hC : bautinC (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have h1' := h1.ne'
  rw [(m.coeff_atoms hp.1.L.ne').2.1] at h1'
  exact mem_den_unstable_of_bautinForm_neg m hp hb hH h1 h0
    (bautinForm_neg_of_cubic _ h1' hp.1.ω0 hG hC)

/-- **A supercritical angle path**: a balanced physical model on the Hopf boundary with
`𝔊_P > 0` and `𝔆_P > 0` at its `(K_p Q, R/L, ω₀)` is locally asymptotically stable, whatever its
angle (`Line.PSC.mem_den_locallyAsymptoticallyStable_of_bautinForm_pos`). -/
@[tmio TM, powerlib_domain] theorem
    mem_den_locallyAsymptoticallyStable_of_bautinG_pos_of_bautinC_pos (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hG : 0 < bautinG (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0)
    (hC : 0 < bautinC (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have h1' := h1.ne'
  rw [(m.coeff_atoms hp.1.L.ne').2.1] at h1'
  exact mem_den_locallyAsymptoticallyStable_of_bautinForm_pos m hp hb hH h1 h0
    (bautinForm_pos_of_cubic _ h1' hp.1.ω0 hG hC)

/-! ## The second Bautin point of the angle path -/

namespace BautinAngle

open Bautin (r r_pos r_sq qv pv3 iotaR piR rotR wv iotaR_apply piR_apply rotR_apply rotR_rotR
  piR_iotaR piR_wv A_wv piR_A_iotaR isChart_R sub_iotaR_piR frameY_rotR lin0 lin1 lin2 pv lowF1
  lowF2 lowF3)

/-- **The second Bautin point of the angle path**: `E = R = L = ω₀ = 1`, `V = 3√2/5`,
`K_p = 20`, `P_ref = 1/2`, `δ* = π/4` (`κ = K_p Q = −2`, `t = 12`). -/
def bpt : Model := ⟨⟨⟨1, 3 * Real.sqrt 2 / 5, 1, 1, 1⟩, 20, 1 / 2⟩, Real.pi / 4⟩

@[tmio M, powerlib_domain] private theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

/-- The operating angle `δ* = π/4`, `cos δ* = sin δ* = √2/2`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_trig :
    Real.cos bpt.δ = Real.sqrt 2 / 2 ∧ Real.sin bpt.δ = Real.sqrt 2 / 2 :=
  ⟨Real.cos_pi_div_four, Real.sin_pi_div_four⟩

/-- The model is physical. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_physical : Meets bpt .physical :=
  ⟨⟨by norm_num [bpt], by simp only [bpt]; positivity, by norm_num [bpt], by norm_num [bpt],
    by norm_num [bpt]⟩, by norm_num [bpt]⟩

/-- The angle is balanced, `P(π/4) = 1/2`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_balanced : Meets bpt .balanced := by
  change bpt.g.qssPower bpt.δ = 1 / 2
  rw [Network.qssPower_eq _ (by norm_num [bpt, Network.absSq, Network.X]), bpt_trig.1,
    bpt_trig.2]
  simp only [bpt, Network.absSq, Network.X]
  ring

/-- The reactive power at the point, `Q = −1/10`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_Q : bpt.Q = -1 / 10 := by
  change bpt.g.qssReactive bpt.δ = -1 / 10
  rw [Network.qssReactive_eq _ (by norm_num [bpt, Network.absSq, Network.X]), bpt_trig.1,
    bpt_trig.2]
  simp only [bpt, Network.absSq, Network.X]
  linear_combination (-3 / 10) * sqrt2_sq

/-- The monic cubic at the point: `a₂ = 4`, `a₁ = 6`, `a₀ = 24` (as at the first point
`Bautin.bpt`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_coeffs :
    bpt.g.coeff2 bpt.Q = 4 ∧ bpt.g.coeff1 bpt.Q = 6 ∧ bpt.g.coeff0 bpt.Q = 24 := by
  rw [bpt_Q]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X, bpt]

/-- The angle term `t = 12 = 2 a₁`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_angleShift : bpt.angleShift = 12 := by
  rw [Model.angleShift, bpt_Q]
  norm_num [bpt]

/-- **The point is degenerate**: on the Hopf boundary with a critical pair at `ω = √6`, and every
critical pair has `ℓ₁ = 0` (`𝔅_P(−2, 1, 1, 12) = 𝔊_P · 12 · (12 − 2 a₁) + a₂ a₁² ℌ_P = 0`,
`Line.PSC.Model.sign_firstLyapunov_crit`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_firstLyapunov :
    (∃ q p : Fin 3 → ℂ, IsCriticalPair bpt.field 0 (Real.sqrt 6) q p) ∧
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

/-- The Jacobian of the rotated frame is that of the first point `Bautin.bpt`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem rotJ_bpt : bpt.rotJ = fderiv ℝ Bautin.bpt.field 0 := by
  rw [Model.rotJ, Bautin.fderiv_field_zero, bpt_Q]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [bpt]

/-- **The linear part in the rotated frame is that of the first point**:
`DF(0) R_{π/4} = R_{π/4} A`, `A = [[−2, −20, 0], [0, −1, 1], [1, −1, −1]]`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem fderiv_rotT (z : State 3) :
    fderiv ℝ bpt.field 0 (rotT bpt.δ z) = rotT bpt.δ (fderiv ℝ Bautin.bpt.field 0 z) := by
  rw [bpt.fderiv_field_rotT (by norm_num [bpt]), rotJ_bpt]

/-- The nonlinear part of the rotated field. -/
def frot (z : State 3) : State 3 := bpt.rotField z - fderiv ℝ Bautin.bpt.field 0 z

/-- **The nonlinearities of the rotated field**: those of the first point with `−10 (cos z₀ − 1)`
in place of `2 (cos z₀ − 1)` (`N = K_p P_ref = 10` instead of `−2`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem frot_apply (z : State 3) (i : Fin 3) :
    frot z i = ![-10 * (Real.cos (z 0) - 1) - 20 * ((Real.cos (z 0) - 1) * z 1 +
      Real.sin (z 0) * z 2) - 2 * (Real.sin (z 0) - z 0), Real.cos (z 0) - 1,
      Real.sin (z 0) - z 0] i := by
  rw [frot, PiLp.sub_apply, Bautin.A_apply]
  fin_cases i
  · simp [Model.rotField, bpt_Q]; norm_num [bpt]; ring
  · simp [Model.rotField, bpt_Q]; norm_num [bpt]
  · simp [Model.rotField, bpt_Q]; norm_num [bpt]

/-- The nonlinear part `f = F − DF(0)` of the grid-frame field. -/
def fnl (x : State 3) : State 3 := bpt.field x - fderiv ℝ bpt.field 0 x

/-- **The nonlinear part in the rotated frame**: `f(R_{π/4} z) = R_{π/4} f_rot(z)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem fnl_rotT (z : State 3) :
    fnl (rotT bpt.δ z) = rotT bpt.δ (frot z) := by
  rw [fnl, Model.field_rotT bpt_physical bpt_balanced, fderiv_rotT, frot, map_sub]

/-- The rotated-frame critical vectors are those of the first point:
`critVecQ 1 1 1 √6 = Bautin.qv`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critQ_eq : bpt.critQ r = rotC bpt.δ qv := by
  have hr : (r : ℂ) ^ 2 = 6 := by rw [← Complex.ofReal_pow, r_sq]; norm_num
  rw [Model.critQ]
  congr 1
  ext i
  fin_cases i <;> simp [critVecQ, qv, bpt]
  · ring_nf; simp only [Complex.I_sq, hr]; ring
  · ring

/-- The rotated-frame left vector is that of the first point (`⟨p, q⟩ = 1`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem critP_eq : bpt.critP r = rotC bpt.δ pv3 := by
  have hr : (r : ℂ) ^ 2 = 6 := by rw [← Complex.ofReal_pow, r_sq]; norm_num
  have hr3 : (r : ℂ) ^ 3 = 6 * r := by rw [pow_succ, hr]
  have hI3 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  have hinv : (starRingEnd ℂ (critPairing 1 (-2) 1 1 r))⁻¹ = -1 / 44 + (r : ℂ) / 66 * I := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    simp [critPairing, map_mul, map_sub, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq, hr, hr3]
    ring
  rw [Model.critP, bpt_Q]
  have e : (bpt.g.E / bpt.g.L) = 1 ∧ bpt.g.Kp * (-1 / 10) = -2 ∧ bpt.g.R / bpt.g.L = 1 ∧
      bpt.g.ω0 = 1 := by norm_num [bpt]
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2, hinv]
  congr 1
  ext i
  fin_cases i <;> simp [critVecL, pv3] <;> ring_nf <;> simp only [Complex.I_sq, hr, hr3, hI3] <;>
    ring

/-- **The critical pair at `ω = √6`**: `(R_{π/4} q, R_{π/4} p)`, `(q, p)` the critical pair of
the first point (`Line.PSC.Model.isCriticalPair_crit`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCriticalPair_bpt :
    IsCriticalPair bpt.field 0 r (rotC bpt.δ qv) (rotC bpt.δ pv3) := by
  obtain ⟨h2, h1, h0⟩ := bpt_coeffs
  rw [← critQ_eq, ← critP_eq]
  exact Model.isCriticalPair_crit bpt_physical bpt_balanced (by rw [h2, h1, h0]; norm_num)
    r_pos (by rw [h1, r_sq])

/-- The grid-frame chart `ι = R_{π/4} ι'` of the critical plane. -/
def iotaG : State 2 →L[ℝ] State 3 := (rotT bpt.δ).comp iotaR

/-- The grid-frame coordinates `π = π' R_{−π/4}`. -/
def piG : State 3 →L[ℝ] State 2 := piR.comp (rotT (-bpt.δ))

/-- `π (R_{π/4} v) = π' v`. Static evidence on the model. -/
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

/-- **`(1 − P)` of a rotated vector**: `R v − ι π (R v) = R ((v₁ − (π' v)₀) w)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem sub_iotaG_piG (v : State 3) :
    rotT bpt.δ v - iotaG (piG (rotT bpt.δ v)) = rotT bpt.δ ((v 1 - piR v 0) • wv) := by
  rw [piG_rotT, iotaG, ContinuousLinearMap.comp_apply, ← map_sub, sub_iotaR_piR]

/-! ## The approximate centre manifold (rotated frame) -/

/-- `h` of the manifold, degree 2. -/
def hL2 : List (ℝ × ℕ × ℕ × ℕ) := [(16 / 55, 2, 0, 0), (-36 / 55, 1, 1, 0), (-1 / 5, 0, 2, 0)]

/-- `10 h`, the angle part of the manifold, degree 2. -/
def aL2 : List (ℝ × ℕ × ℕ × ℕ) := [(32 / 11, 2, 0, 0), (-72 / 11, 1, 1, 0), (-2, 0, 2, 0)]

/-- `−3 h`, the `i_q` part of the manifold, degree 2. -/
def cL2 : List (ℝ × ℕ × ℕ × ℕ) := [(-48 / 55, 2, 0, 0), (108 / 55, 1, 1, 0), (3 / 5, 0, 2, 0)]

/-- `h` of the manifold, degree 3. -/
def hL3 : List (ℝ × ℕ × ℕ × ℕ) := [(992 / 231, 3, 0, 0), (-904 / 847, 2, 1, 0), (76 / 847, 1, 2, 0),
    (-100 / 231, 0, 3, 0)]

/-- `10 h`, the angle part of the manifold, degree 3. -/
def aL3 : List (ℝ × ℕ × ℕ × ℕ) := [(9920 / 231, 3, 0, 0), (-9040 / 847, 2, 1, 0), (760 / 847, 1, 2,
    0), (-1000 / 231, 0, 3, 0)]

/-- `−3 h`, the `i_q` part of the manifold, degree 3. -/
def cL3 : List (ℝ × ℕ × ℕ × ℕ) := [(-992 / 77, 3, 0, 0), (2712 / 847, 2, 1, 0), (-228 / 847, 1, 2,
    0), (100 / 77, 0, 3, 0)]

/-- `h` of the manifold, degree 4. -/
def hL4 : List (ℝ × ℕ × ℕ × ℕ) := [(2497412 / 139755, 4, 0, 0), (423736 / 139755, 3, 1, 0), (39716 /
    4235, 2, 2, 0), (-52948 / 19965, 1, 3, 0), (-283 / 12705, 0, 4, 0)]

/-- `10 h`, the angle part of the manifold, degree 4. -/
def aL4 : List (ℝ × ℕ × ℕ × ℕ) := [(4994824 / 27951, 4, 0, 0), (847472 / 27951, 3, 1, 0), (79432 /
    847, 2, 2, 0), (-105896 / 3993, 1, 3, 0), (-566 / 2541, 0, 4, 0)]

/-- `−3 h`, the `i_q` part of the manifold, degree 4. -/
def cL4 : List (ℝ × ℕ × ℕ × ℕ) := [(-2497412 / 46585, 4, 0, 0), (-423736 / 46585, 3, 1, 0), (-119148
    / 4235, 2, 2, 0), (52948 / 6655, 1, 3, 0), (283 / 4235, 0, 4, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low1L4 : List (ℝ × ℕ × ℕ × ℕ) := [(80, 2, 0, 0), (40, 1, 1, 0), (-40, 0, 2, 0), (32, 3, 0, 0),
    (1152 / 11, 2, 1, 0), (1984 / 11, 1, 2, 0), (16, 0, 3, 0), (-1895808 / 847, 4, 0, 0), (59648 /
    121, 3, 1, 0), (28928 / 77, 2, 2, 0), (112544 / 847, 1, 3, 0), (5952 / 77, 0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low1L5 : List (ℝ × ℕ × ℕ × ℕ) := [(-7332320 / 847, 5, 0, 0), (-172085120 / 27951, 4, 1, 0),
    (-142849760 / 27951, 3, 2, 0), (16279840 / 9317, 2, 3, 0), (13251160 / 27951, 1, 4, 0), (102560
    / 2541, 0, 5, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low2L4 : List (ℝ × ℕ × ℕ × ℕ) := [(-8, 2, 0, 0), (8, 1, 1, 0), (-2, 0, 2, 0), (128 / 11, 3, 0,
    0), (-32, 2, 1, 0), (56 / 11, 1, 2, 0), (4, 0, 3, 0), (150944 / 847, 4, 0, 0), (-110848 / 847,
    3, 1, 0), (21456 / 847, 2, 2, 0), (-31792 / 847, 1, 3, 0), (564 / 77, 0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low2L5 : List (ℝ × ℕ × ℕ × ℕ) := [(15620128 / 27951, 5, 0, 0), (1792400 / 9317, 4, 1, 0),
    (6183680 / 27951, 3, 2, 0), (-7610480 / 27951, 2, 3, 0), (306360 / 9317, 1, 4, 0), (-27644 /
    2541, 0, 5, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low3L4 : List (ℝ × ℕ × ℕ × ℕ) := [(32 / 3, 3, 0, 0), (-16, 2, 1, 0), (8, 1, 2, 0), (-4 / 3, 0,
    3, 0), (-256 / 11, 4, 0, 0), (832 / 11, 3, 1, 0), (-464 / 11, 2, 2, 0), (-32 / 11, 1, 3, 0), (4,
    0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low3L5 : List (ℝ × ℕ × ℕ × ℕ) := [(-1419392 / 4235, 5, 0, 0), (309696 / 847, 4, 1, 0), (-84096 /
    847, 3, 2, 0), (80448 / 847, 2, 3, 0), (-48512 / 847, 1, 4, 0), (1896 / 385, 0, 5, 0)]

/-- The jet of the first chart coordinate, degree 2. -/
def cF2 : List (ℝ × ℕ × ℕ × ℕ) := [(-144 / 11, 2, 0, 0), (84 / 11, 1, 1, 0), (-6 / 11, 0, 2, 0)]

/-- The jet of the second chart coordinate, degree 2. -/
def cG2 : List (ℝ × ℕ × ℕ × ℕ) := [(312 / 11, 2, 0, 0), (-72 / 11, 1, 1, 0), (-42 / 11, 0, 2, 0)]

/-- The jet of the first chart coordinate, degree 3. -/
def cF3 : List (ℝ × ℕ × ℕ × ℕ) := [(5168 / 363, 3, 0, 0), (-5504 / 121, 2, 1, 0), (-8 / 11, 1, 2,
    0), (124 / 33, 0, 3, 0)]

/-- The jet of the second chart coordinate, degree 3. -/
def cG3 : List (ℝ × ℕ × ℕ × ℕ) := [(-1376 / 121, 3, 0, 0), (8464 / 121, 2, 1, 0), (288 / 11, 1, 2,
    0), (-48 / 11, 0, 3, 0)]

/-- The jet of the first chart coordinate, degree 4. -/
def cF4 : List (ℝ × ℕ × ℕ × ℕ) := [(2870752 / 9317, 4, 0, 0), (-1521664 / 9317, 3, 1, 0), (48368 /
    9317, 2, 2, 0), (-43136 / 847, 1, 3, 0), (452 / 77, 0, 4, 0)]

/-- The jet of the second chart coordinate, degree 4. -/
def cG4 : List (ℝ × ℕ × ℕ × ℕ) := [(-6718688 / 9317, 4, 0, 0), (3133376 / 9317, 3, 1, 0), (121568 /
    9317, 2, 2, 0), (10672 / 121, 1, 3, 0), (192 / 77, 0, 4, 0)]

/-- The jet of the first chart coordinate, degree 5. -/
def cF5 : List (ℝ × ℕ × ℕ × ℕ) := [(1526544848 / 1537305, 5, 0, 0), (176386096 / 307461, 4, 1, 0),
    (48754128 / 102487, 3, 2, 0), (-16863776 / 43923, 2, 3, 0), (192788 / 27951, 1, 4, 0), (-58428 /
    4235, 0, 5, 0)]

/-- The jet of the second chart coordinate, degree 5. -/
def cG5 : List (ℝ × ℕ × ℕ × ℕ) := [(-577728224 / 219615, 5, 0, 0), (-59382448 / 43923, 4, 1, 0),
    (-137171648 / 102487, 3, 2, 0), (250242512 / 307461, 2, 3, 0), (385192 / 27951, 1, 4, 0),
    (116348 / 4235, 0, 5, 0)]

/-- The polynomial part of the defect, degrees five to eight. -/
def highD : List (ℝ × ℕ × ℕ × ℕ) := [(-201135808 / 307461, 5, 0, 0), (10796480 / 43923, 4, 1, 0),
    (-149637520 / 307461, 3, 2, 0), (5064800 / 43923, 2, 3, 0), (-13034200 / 307461, 1, 4, 0),
    (2395424 / 307461, 0, 5, 0), (4534301696 / 4611915, 6, 0, 0), (-52813501696 / 16910355, 5, 1,
    0), (4339684864 / 3382071, 4, 2, 0), (-7169658368 / 10146213, 3, 3, 0), (-524931104 / 3382071,
    2, 4, 0), (161095744 / 1537305, 1, 5, 0), (-44165776 / 4611915, 0, 6, 0)]

/-- `h`, degrees two to four. -/
def hL : List (ℝ × ℕ × ℕ × ℕ) := hL2 ++ hL3 ++ hL4

/-- The graph in the rotated chart coordinates, `H(y) = h(y) w`. -/
def manifoldH (y : State 2) : State 3 := poly3 hL (y 0) (y 1) 0 • wv

/-- The graph in grid coordinates, `R_{π/4} H(y)`. -/
def manifoldG (y : State 2) : State 3 := rotT bpt.δ (manifoldH y)

/-- **The order-four approximate centre manifold** `φ(x) = R_{π/4} H(π x)`. -/
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

/-- The derivative of the grid-frame graph `R_{π/4} H`. -/
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

/-- The grid-frame point of the manifold over `y`: `ι y + φ(ι y) = R_{π/4} (ι' y + H y)`.
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
  have hA : fderiv ℝ bpt.field 0 (iotaG y) =
      rotT bpt.δ (fderiv ℝ Bautin.bpt.field 0 (iotaR y)) := by
    rw [iotaG, ContinuousLinearMap.comp_apply, fderiv_rotT]
  rw [chartField, iotaG_add_manifold, hA, fnl_rotT, ← map_add, piG_rotT, map_add, piR_A_iotaR]

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

/-- The chart coordinates of `f_rot` on the manifold. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem G_eq (y : State 2) :
    G0 y = -1 / 22 * f0v y + 13 / 11 * (Real.cos (tv y) - 1) +
        2 / 11 * (Real.sin (tv y) - tv y) ∧
      G1 y = 2 / 11 * f0v y - 19 / 11 * (Real.cos (tv y) - 1) +
        3 / 11 * (Real.sin (tv y) - tv y) := by
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
    (fun y : State 2 => lin0 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 := lin_isBigO (-4) 2

@[tmio M, powerlib_domain] private theorem o_l1 :
    (fun y : State 2 => lin1 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (lin_isBigO 1 0).congr_left fun y => by simp only [lin1]; ring

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
    pv cF y = -1 / 22 * pv low1L y + 13 / 11 * pv low2L y + 2 / 11 * pv low3L y := by
  simp only [pv, cF, cF2, cF3, cF4, cF5, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L,
    low3L4, low3L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The jet of the second chart coordinate from the truncated nonlinearities. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem cG_eq (y : State 2) :
    pv cG y = 2 / 11 * pv low1L y - 19 / 11 * pv low2L y + 3 / 11 * pv low3L y := by
  simp only [pv, cG, cG2, cG3, cG4, cG5, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L,
    low3L4, low3L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- **The first chart coordinate has the jet `cF`**: `G₀ − cF = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G0_sub_jet :
    (fun y => G0 y - pv cF y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((f1_sub_low.const_mul_left (-1 / 22)).add
    (f2_sub_low.const_mul_left (13 / 11))).add
      (f3_sub_low.const_mul_left (2 / 11))).congr_left fun y => ?_
  rw [(G_eq y).1, cF_eq]
  ring

/-- **The second chart coordinate has the jet `cG`**: `G₁ − cG = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G1_sub_jet :
    (fun y => G1 y - pv cG y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((f1_sub_low.const_mul_left (2 / 11)).add
    (f2_sub_low.const_mul_left (-19 / 11))).add
      (f3_sub_low.const_mul_left (3 / 11))).congr_left fun y => ?_
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
  dpoly3 hL (y 0) (y 1) 0 (y 1 + G0 y) (-6 * y 0 + G1 y) 0 + 4 * pv hL y -
    (Real.cos (tv y) - 1) + G0 y

/-- **The homological equations make the polynomial part of the defect of degree at least five**
(`highD` has degrees five to eight). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main_eq_high (y : State 2) :
    dpoly3 hL (y 0) (y 1) 0 (y 1 + pv (cF2 ++ cF3) y) (-6 * y 0 + pv (cG2 ++ cG3) y) 0 +
      4 * pv hL y - pv low2L4 y + pv (cF2 ++ cF3 ++ cF4) y = pv highD y := by
  simp only [dpoly3_cons, dpoly3_nil, poly3_cons, poly3_nil, hL, hL2, hL3, hL4, cF2, cF3, cF4,
    cG2, cG3, low2L4, highD, pv, List.cons_append, List.nil_append]
  ring

/-- **The invariance defect at a chart point** is `R_{π/4} (d(y) w)`. Static evidence on the
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
      rotT bpt.δ ((-4 * pv hL y + (Real.cos (tv y) - 1 - G0 y)) • wv) := by
    rw [normalField, iotaG_add_manifold, hφ]
    simp only [_root_.sub_apply, one_apply_eq_self, hP]
    have hA : fderiv ℝ bpt.field 0 (manifoldG y) = rotT bpt.δ ((-4 * pv hL y) • wv) := by
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
      (Real.cos (tv y) - 1 - pv low2L4 y) + (G0 y - pv (cF2 ++ cF3 ++ cF4) y) := by
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
      hG0_4).congr_left fun y => ?_
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

/-- The normalised jet `J/ω` (`τ = ωt`, `ω = √6`). -/
def jetN : Jet5 where
  a20 := (-24 / 11 * r)
  a11 := (-84 / 11)
  a02 := (-6 / 11 * r)
  b20 := (-52 / 11)
  b11 := (-12 / 11 * r)
  b02 := (42 / 11)
  a30 := (2584 / 1089 * r)
  a21 := (5504 / 121)
  a12 := (-8 / 11 * r)
  a03 := (-248 / 11)
  b30 := (688 / 363)
  b21 := (4232 / 363 * r)
  b12 := (-288 / 11)
  b03 := (-48 / 11 * r)
  a40 := (1435376 / 27951 * r)
  a31 := (1521664 / 9317)
  a22 := (48368 / 9317 * r)
  a13 := (258816 / 847)
  a04 := (2712 / 77 * r)
  b40 := (3359344 / 27951)
  b31 := (1566688 / 27951 * r)
  b22 := (-121568 / 9317)
  b13 := (10672 / 121 * r)
  b04 := (-1152 / 77)
  a50 := (763272424 / 4611915 * r)
  a41 := (-176386096 / 307461)
  a32 := (48754128 / 102487 * r)
  a23 := (33727552 / 14641)
  a14 := (385576 / 9317 * r)
  a05 := (2103408 / 4235)
  b50 := (288864112 / 658845)
  b41 := (-29691224 / 131769 * r)
  b32 := (137171648 / 102487)
  b23 := (250242512 / 307461 * r)
  b14 := (-770384 / 9317)
  b05 := (698088 / 4235 * r)

/-- The quintic jet of the chart field in the rotation coordinates of `rotR`. -/
def jet : Jet5 where
  a20 := r * (-24 / 11 * r)
  a11 := r * (-84 / 11)
  a02 := r * (-6 / 11 * r)
  b20 := r * (-52 / 11)
  b11 := r * (-12 / 11 * r)
  b02 := r * (42 / 11)
  a30 := r * (2584 / 1089 * r)
  a21 := r * (5504 / 121)
  a12 := r * (-8 / 11 * r)
  a03 := r * (-248 / 11)
  b30 := r * (688 / 363)
  b21 := r * (4232 / 363 * r)
  b12 := r * (-288 / 11)
  b03 := r * (-48 / 11 * r)
  a40 := r * (1435376 / 27951 * r)
  a31 := r * (1521664 / 9317)
  a22 := r * (48368 / 9317 * r)
  a13 := r * (258816 / 847)
  a04 := r * (2712 / 77 * r)
  b40 := r * (3359344 / 27951)
  b31 := r * (1566688 / 27951 * r)
  b22 := r * (-121568 / 9317)
  b13 := r * (10672 / 121 * r)
  b04 := r * (-1152 / 77)
  a50 := r * (763272424 / 4611915 * r)
  a41 := r * (-176386096 / 307461)
  a32 := r * (48754128 / 102487 * r)
  a23 := r * (33727552 / 14641)
  a14 := r * (385576 / 9317 * r)
  a05 := r * (2103408 / 4235)
  b50 := r * (288864112 / 658845)
  b41 := r * (-29691224 / 131769 * r)
  b32 := r * (137171648 / 102487)
  b23 := r * (250242512 / 307461 * r)
  b14 := r * (-770384 / 9317)
  b05 := r * (698088 / 4235 * r)

/-- The jet in the rotation frame is the chart jet: `F_J(a, Y) = cF(a, −√6 Y)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem jetF_frame (a Y : ℝ) :
    poly3 jet.F a Y 0 = poly3 cF a (-(r * Y)) 0 := by
  simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4,
    PlanarFocus.Jet5.F5, jet, cF, cF2, cF3, cF4, cF5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  linear_combination (763272424*a ^ 5/4611915 + 1435376*a ^ 4/27951 + 2584*a ^ 3/1089 - 16863776*a ^
    2*Y ^ 3*r/43923 - 24*a ^ 2/11 - 192788*a*Y ^ 4*r ^ 2/27951 - 43136*a*Y ^ 3*r/847 - 58428*Y ^ 5*r
    ^ 3/4235 - 350568*Y ^ 5*r/4235 - 452*Y ^ 4*r ^ 2/77 + 124*Y ^ 3*r/33) * r_sq

/-- The jet in the rotation frame is the chart jet: `√6 G_J(a, Y) = −cG(a, −√6 Y)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem jetG_frame (a Y : ℝ) :
    r * poly3 jet.G a Y 0 = -poly3 cG a (-(r * Y)) 0 := by
  simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet.G2, PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4,
    PlanarFocus.Jet5.G5, jet, cG, cG2, cG3, cG4, cG5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  linear_combination (288864112*a ^ 5/658845 - 29691224*a ^ 4*Y*r/131769 + 3359344*a ^ 4/27951 +
    1566688*a ^ 3*Y*r/27951 + 688*a ^ 3/363 + 4232*a ^ 2*Y*r/363 - 52*a ^ 2/11 + 385192*a*Y ^ 4*r ^
    2/27951 - 12*a*Y*r/11 - 116348*Y ^ 5*r ^ 3/4235 + 192*Y ^ 4*r ^ 2/77) * r_sq

/-- The normalised jet (`τ = √6 t`): `J/√6 = jetN`. -/
@[tmio M, powerlib_domain] theorem jet_nrm : jet.nrm r = jetN := by
  have h : r ≠ 0 := r_pos.ne'
  simp only [PlanarFocus.Jet5.nrm, jet, jetN, mul_div_cancel_left₀ _ h]

/-- The Lyapunov chain of the normalised jet: `c30` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c30 : jetN.c30 1 = (-104 / 33) := by
  simp only [PlanarFocus.Jet.c30]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c21` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c21 : jetN.c21 1 = (48 / 11 * r) := by
  simp only [PlanarFocus.Jet.c21]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c12` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c12 : jetN.c12 1 = (84 / 11) := by
  simp only [PlanarFocus.Jet.c12]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c03` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c03 : jetN.c03 1 = (4 * r) := by
  simp only [PlanarFocus.Jet.c03]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `d40` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d40 : jetN.d40 1 = (-2084 / 33) := by
  simp only [PlanarFocus.Jet.d40]
  simp only [jetN]
  linear_combination (-1260/121) * r_sq

/-- The Lyapunov chain of the normalised jet: `d31` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d31 : jetN.d31 1 = (-5168 / 1089 * r) := by
  simp only [PlanarFocus.Jet.d31]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `d22` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d22 : jetN.d22 1 = (-12376 / 121) := by
  simp only [PlanarFocus.Jet.d22]
  simp only [jetN]
  linear_combination (-1080/121) * r_sq

/-- The Lyapunov chain of the normalised jet: `d13` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d13 : jetN.d13 1 = (3984 / 121 * r) := by
  simp only [PlanarFocus.Jet.d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `l1` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l1 : jetN.l1 1 = (0) := by
  simp only [PlanarFocus.Jet.l1]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r50 : jetN.r50 1 = (18506848 / 27951 * r) := by
  simp only [PlanarFocus.Jet5.r50]
  rw [jv_c30, jv_c21, jv_d40, jv_d31]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r41 : jetN.r41 1 = (14809376 / 3993) := by
  simp only [PlanarFocus.Jet5.r41]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22]
  simp only [jetN]
  linear_combination (430528/3993) * r_sq

/-- The Lyapunov chain of the normalised jet: `r32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r32 : jetN.r32 1 = (29681984 / 27951 * r) := by
  simp only [PlanarFocus.Jet5.r32]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r23 : jetN.r23 1 = (1574368 / 1331) := by
  simp only [PlanarFocus.Jet5.r23]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (-76288/1331) * r_sq

/-- The Lyapunov chain of the normalised jet: `r14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r14 : jetN.r14 1 = (-922448 / 9317 * r) := by
  simp only [PlanarFocus.Jet5.r14]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r05 : jetN.r05 1 = (-5814048 / 9317) := by
  simp only [PlanarFocus.Jet5.r05]
  rw [jv_c12, jv_c03, jv_d13]
  simp only [jetN]
  linear_combination (-93600/1331) * r_sq

/-- The Lyapunov chain of the normalised jet: `e50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e50 : jetN.e50 1 = (15838880 / 27951) := by
  simp only [PlanarFocus.Jet5.e50]
  rw [jv_r41, jv_r23, jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e41 : jetN.e41 1 = (-18506848 / 27951 * r) := by
  simp only [PlanarFocus.Jet5.e41]
  rw [jv_r50]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e32 : jetN.e32 1 = (-12235616 / 27951) := by
  simp only [PlanarFocus.Jet5.e32]
  rw [jv_r23, jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e23 : jetN.e23 1 = (-11523264 / 9317 * r) := by
  simp only [PlanarFocus.Jet5.e23]
  rw [jv_r50, jv_r32]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e14 : jetN.e14 1 = (-5814048 / 9317) := by
  simp only [PlanarFocus.Jet5.e14]
  rw [jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e05 : jetN.e05 1 = (-402256 / 847 * r) := by
  simp only [PlanarFocus.Jet5.e05]
  rw [jv_r50, jv_r32, jv_r14]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r60 : jetN.r60 1 = (-722588912 / 219615 * r) := by
  simp only [PlanarFocus.Jet5.r60]
  rw [jv_c30, jv_c21, jv_d40, jv_d31, jv_e50, jv_e41]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r51 : jetN.r51 1 = (61208801408 / 4611915) := by
  simp only [PlanarFocus.Jet5.r51]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22, jv_e50, jv_e41, jv_e32]
  simp only [jetN]
  linear_combination (6553018240/922383) * r_sq

/-- The Lyapunov chain of the normalised jet: `r42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r42 : jetN.r42 1 = (11990813936 / 307461 * r) := by
  simp only [PlanarFocus.Jet5.r42]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e50, jv_e41, jv_e32,
    jv_e23]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r33 : jetN.r33 1 = (32342230912 / 307461) := by
  simp only [PlanarFocus.Jet5.r33]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e41, jv_e32, jv_e23,
    jv_e14]
  simp only [jetN]
  linear_combination (4074728192/307461) * r_sq

/-- The Lyapunov chain of the normalised jet: `r24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r24 : jetN.r24 1 = (2688400080 / 102487 * r) := by
  simp only [PlanarFocus.Jet5.r24]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13, jv_e32, jv_e23, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r15 : jetN.r15 1 = (212178048 / 6655) := by
  simp only [PlanarFocus.Jet5.r15]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13, jv_e23, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (497112192/102487) * r_sq

/-- The Lyapunov chain of the normalised jet: `r06` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r06 : jetN.r06 1 = (-4637265264 / 512435 * r) := by
  simp only [PlanarFocus.Jet5.r06]
  rw [jv_c12, jv_c03, jv_d13, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f60 : jetN.f60 1 = (20491587296 / 1257795) := by
  simp only [PlanarFocus.Jet5.f60]
  rw [jv_r51, jv_r33, jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f51 : jetN.f51 1 = (5397527384 / 1537305 * r) := by
  simp only [PlanarFocus.Jet5.f51]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f42 : jetN.f42 1 = (64934353184 / 1537305) := by
  simp only [PlanarFocus.Jet5.f42]
  rw [jv_r33, jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f33 : jetN.f33 1 = (-2129881184 / 307461 * r) := by
  simp only [PlanarFocus.Jet5.f33]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f24 : jetN.f24 1 = (106089024 / 6655) := by
  simp only [PlanarFocus.Jet5.f24]
  rw [jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f15 : jetN.f15 1 = (-4750400264 / 512435 * r) := by
  simp only [PlanarFocus.Jet5.f15]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `k6` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_k6 : jetN.k6 1 = (17000 / 77 * r) := by
  simp only [PlanarFocus.Jet5.k6]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `l2` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l2 : jetN.l2 1 = (34000 / 77 * r) := by
  simp only [PlanarFocus.Jet5.l2]
  rw [jv_k6]
  linear_combination (0) * r_sq

/-- `l₁(J) = 0` at the degenerate point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1_eq_zero : jet.l1 r = 0 := by
  rw [← PlanarFocus.Jet5.l1_nrm jet r r_pos.ne', jet_nrm, jv_l1]

/-- **`l₂(J) = 34000√6/77 > 0` at the second degenerate point.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l2_eq : jet.l2 r = 34000 / 77 * r := by
  rw [← PlanarFocus.Jet5.l2_nrm jet r r_pos.ne', jet_nrm, jv_l2]

end BautinAngle

open BautinAngle in
/-- **The second Bautin point of the angle path is unstable**: at `V = 3√2/5`, `K_p = 20`,
`P_ref = 1/2`, `δ* = π/4` on the unit line (`ℓ₁ = 0`, `Line.PSC.BautinAngle.bpt_firstLyapunov`)
the model is a weak focus of the second order with `l₂ = 34000√6/77 > 0`, read in the chart
`ι = R_{π/4} ι'`, `π = π' R_{−π/4}` of the critical plane (the approximate centre manifold
`BautinAngle.manifold`, invariance defect `O(‖u‖⁵)`, the quintic jet `BautinAngle.jet`;
`mem_den_unstable_of_secondLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem angle_bautin_mem_den_unstable :
    connection% (BautinAngle.bpt ∈ family.den (.flow .unstable)) := by
  obtain ⟨h2, h1, h0⟩ := bpt_coeffs
  have hr0 : Bautin.r ≠ 0 := Bautin.r_pos.ne'
  refine mem_den_unstable_of_secondLyapunov_pos bpt (by rw [h1]; norm_num)
    (by rw [h0]; norm_num) (by rw [h2, h1, h0]; norm_num) isCriticalPair_bpt isChart_G
    Bautin.rotR_rotR ⟨contDiffAt_manifold, manifold_zero, fderiv_manifold_zero, critP_manifold⟩
    isOrder_defect (J := jet) ⟨?_, ?_⟩
    ⟨jet_l1_eq_zero, by rw [jet_l2_eq]; exact mul_pos (by norm_num) Bautin.r_pos⟩
  · refine (G0_sub_jet.trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => bpt.field x - fderiv ℝ bpt.field 0 x) = fnl from rfl, chartField_eq,
      Bautin.frameY_rotR, jetF_frame, show -(Bautin.r * (-Bautin.r⁻¹ * y 1)) = y 1 by field_simp]
    simp only [PlanarFocus.frameX_apply, PiLp.add_apply, (Bautin.rotR_apply y).1, G0, Bautin.pv]
    field_simp
    ring
  · refine ((G1_sub_jet.const_mul_left (-Bautin.r⁻¹)).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    have hG := jetG_frame (y 0) (-Bautin.r⁻¹ * y 1)
    rw [show -(Bautin.r * (-Bautin.r⁻¹ * y 1)) = y 1 by field_simp] at hG
    have hG' : poly3 jet.G (y 0) (-Bautin.r⁻¹ * y 1) 0 =
        -Bautin.r⁻¹ * poly3 cG (y 0) (y 1) 0 := by
      have e : poly3 cG (y 0) (y 1) 0 = -(Bautin.r * poly3 jet.G (y 0) (-Bautin.r⁻¹ * y 1) 0) := by
        linarith
      rw [e]; field_simp
    rw [show (fun x => bpt.field x - fderiv ℝ bpt.field 0 x) = fnl from rfl, chartField_eq,
      Bautin.frameY_rotR, Bautin.frameY_rotR, PlanarFocus.frameX_apply, hG']
    simp only [PiLp.add_apply, (Bautin.rotR_apply y).2, G1, Bautin.pv]
    have h6 : (6 : ℝ) = Bautin.r ^ 2 := Bautin.r_sq.symm
    field_simp
    rw [h6]
    ring

end PSC
end powerlib.GFM.Line
