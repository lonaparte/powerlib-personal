import theorem.GridTiedConverter.GFM.HopfBautinData
import theorem.Dynamics.CenterManifoldChart

/-! # The Bautin point of the four-state VSM is unstable (second Lyapunov coefficient)

Model boundary.
* The path `Line.VSM.bautinPath s` (`s > 0`) of zero-current points on the Hopf boundary of the
  four-state VSM on a dynamic R–L line, `theorem/GridTiedConverter/GFM/HopfBautinLine.lean`
  (`E = V = 1`, `R = s`, `L = ω₀ = 1`, `M = 1/(4 + s²)`, `D = 2/(s(4 + s²))`, `P_ref = 0`,
  `δ* = 0`, state `(δ, ω, i_d, i_q)` translated to the operating point), and its degenerate point
  `s*`, the unique positive zero of `bautinNum` (`s* ∈ (2, 21/10)`), where `ℓ₁ = 0`.
* Read in the critical chart of `(bautinPathQ s, bautinPathP s)` at `ω = 1`:
  `ι = critι q`, `π = critπ p`, `P = ι π`, the nonlinear part `f = F − DF(0)` (`Bautin.fnl`).
* The approximate centre manifold `Bautin.manifold s = H ∘ π` is defined for every `s > 0`:
  `H(y) = h₁(y) w₁ + h₂(y) w₂` with polynomials `h₁`, `h₂` of degrees two to four whose
  coefficients are the exact rational functions of
  `theorem/GridTiedConverter/GFM/HopfBautinData.lean`,
  `w₁ = (−1, s + 4/s, 1, 0)`, `w₂ = (−2/s, 1 + 4/s², 0, 1)` spanning `ker π`.
* Level: exact. The trigonometric nonlinearities enter through the sixth-order Taylor remainders
  of `cos` and `sin` (`Dynamics.cos_sub_taylor_isBigO`, `Dynamics.sin_sub_taylor5_isBigO`);
  the polynomial part of the invariance defect vanishes in degrees two to four by the
  homological identities `Bautin.Hom2_ij_eq`, `Bautin.Hom3_ij_eq`, valid for every `s > 0`;
  the signs at `s*` are exact (`Bautin.L2V_pos`). No floating point, sampling or search.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3 (Bautin points,
the second Lyapunov coefficient); Carr, *Applications of Centre Manifold Theory* (1981), §2.4–2.5
(reduction principle, approximation of the centre manifold). The generic laws are
`theorem/Dynamics/CenterReductionBautin.lean` (through
`Line.VSM.mem_den_unstable_of_secondLyapunov_pos`), `theorem/Dynamics/CenterManifoldChart.lean`
(defect in a chart, Taylor remainders) and `theorem/Dynamics/PolyCertificate.lean`; the
coefficients were derived with SymPy over `ℚ(s)` (untrusted, discovery evidence only) and every
identity is checked by the kernel.

Results.
* The manifold: `Bautin.h1L`, `Bautin.h2L`, `Bautin.aL2` … `Bautin.aL4`, `Bautin.w1`, `Bautin.w2`,
  `Bautin.manifoldH`,
  `Bautin.manifold`; `Bautin.contDiffAt_manifold`, `Bautin.manifold_zero`,
  `Bautin.fderiv_manifold_zero`, `Bautin.critP_manifold` (the hypotheses on `φ`).
* The model in the chart: `Bautin.fnl`, `Bautin.fderiv_field_zero`, `Bautin.A_apply`,
  `Bautin.fnl_apply`, `Bautin.critι_bautin`, `Bautin.critπ_bautin`, `Bautin.ker_decomp`
  (`ker π = span(w₁, w₂)`), `Bautin.chartField_eq`.
* The quintic jet of the chart field: `Bautin.f1_sub_low`, `Bautin.f2_sub_low`, `Bautin.f3_sub_low`
  (each nonlinearity minus its weight-five truncation is `O(‖y‖⁶)`), `Bautin.G0_sub_jet`,
  `Bautin.G1_sub_jet` (the chart field has the jet `Bautin.jet s` up to `O(‖y‖⁶)`).
* **The invariance defect is `O(‖u‖⁵)`**: `Bautin.defect_eq` (the defect at `ι y` is
  `d₂(y) w₁ + d₃(y) w₂`), `Bautin.dcomp2_isBigO`, `Bautin.dcomp3_isBigO`,
  `Bautin.isOrder_defect`.
* `Bautin.jet_l1_eq_zero`, `Bautin.jet_l2_pos`: at a zero of `bautinNum` in `(2, 21/10)`,
  `l₁(J) = 0` and `l₂(J) > 0`.
* Steps: `Bautin.x0_eq`, `Bautin.chartPt_apply`, `Bautin.G_eq`, `Bautin.pE_*_eq` (the products of
  pieces), `Bautin.low1_eq` … `Bautin.low3_eq`, `Bautin.split1_isBigO` … `Bautin.split3_isBigO`,
  `Bautin.jetF_eq`, `Bautin.jetG_eq`, `Bautin.jet_tail_bounds`, `Bautin.main2_eq`,
  `Bautin.main3_eq`, `Bautin.main2_eq_high`, `Bautin.main3_eq_high`, `Bautin.critπ_w1`,
  `Bautin.critπ_w2`, `Bautin.DETV_ne`, `Bautin.critπ_manifoldH`, `Bautin.hasFDerivAt_manifoldH`.

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* **`Line.VSM.bautinPath_mem_den_unstable_of_bautinNum_eq_zero`**: the degenerate Hopf point of the
  path (`bautinNum s = 0`, `s > 0`, i.e. `s = s*`) is unstable: a weak focus of the second order
  with `l₂ > 0` (`Line.VSM.mem_den_unstable_of_secondLyapunov_pos`). The points of the path with
  `ℓ₁ ≠ 0` are decided by the first-coefficient laws
  (`bautinPath_mem_den_locallyAsymptoticallyStable`, `bautinPath_mem_den_unstable`,
  `exists_sign_firstLyapunov_eq_sign_sub`).
-/

noncomputable section
namespace powerlib.GFM.Line.VSM

open Filter Topology Asymptotics
open powerlib.Dynamics (State)
open powerlib.Dynamics.Degenerate
open powerlib.Dynamics.CenterManifold
open powerlib.Dynamics.PolyCertificate

namespace Bautin

/-! ## The approximate centre manifold -/

/-- `h₁ = x₂` of the manifold, degree 2. -/
def h1L2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CM1_20 s, 2, 0, 0), (CM1_11 s, 1, 1, 0), (CM1_02 s, 0, 2, 0)]

/-- `h₁ = x₂` of the manifold, degree 3. -/
def h1L3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CM1_30 s, 3, 0, 0), (CM1_21 s, 2, 1, 0), (CM1_12 s, 1, 2, 0), (CM1_03 s, 0, 3, 0)]

/-- `h₁ = x₂` of the manifold, degree 4. -/
def h1L4 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CM1_40 s, 4, 0, 0), (CM1_31 s, 3, 1, 0), (CM1_22 s, 2, 2, 0), (CM1_13 s, 1, 3, 0),
   (CM1_04 s, 0, 4, 0)]

/-- `h₂ = x₃` of the manifold, degree 2. -/
def h2L2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CM2_20 s, 2, 0, 0), (CM2_11 s, 1, 1, 0), (CM2_02 s, 0, 2, 0)]

/-- `h₂ = x₃` of the manifold, degree 3. -/
def h2L3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CM2_30 s, 3, 0, 0), (CM2_21 s, 2, 1, 0), (CM2_12 s, 1, 2, 0), (CM2_03 s, 0, 3, 0)]

/-- `h₂ = x₃` of the manifold, degree 4. -/
def h2L4 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CM2_40 s, 4, 0, 0), (CM2_31 s, 3, 1, 0), (CM2_22 s, 2, 2, 0), (CM2_13 s, 1, 3, 0),
   (CM2_04 s, 0, 4, 0)]

/-- `x₀ = −h₁ − (2/s) h₂` of the manifold, degree 2. -/
def aL2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CA_20 s, 2, 0, 0), (CA_11 s, 1, 1, 0), (CA_02 s, 0, 2, 0)]

/-- `x₀ = −h₁ − (2/s) h₂` of the manifold, degree 3. -/
def aL3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CA_30 s, 3, 0, 0), (CA_21 s, 2, 1, 0), (CA_12 s, 1, 2, 0), (CA_03 s, 0, 3, 0)]

/-- `x₀ = −h₁ − (2/s) h₂` of the manifold, degree 4. -/
def aL4 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(CA_40 s, 4, 0, 0), (CA_31 s, 3, 1, 0), (CA_22 s, 2, 2, 0), (CA_13 s, 1, 3, 0),
   (CA_04 s, 0, 4, 0)]

/-- `h₁ = x₂` of the manifold, degrees two to four. -/
def h1L (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := h1L2 s ++ h1L3 s ++ h1L4 s

/-- `h₂ = x₃` of the manifold, degrees two to four. -/
def h2L (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := h2L2 s ++ h2L3 s ++ h2L4 s

/-- `w₁ = (−1, s + 4/s, 1, 0)`, the first vector of `ker π`. -/
def w1 (s : ℝ) : State 4 := WithLp.toLp 2 ![-1, s + 4 / s, 1, 0]

/-- `w₂ = (−2/s, 1 + 4/s², 0, 1)`, the second vector of `ker π`. -/
def w2 (s : ℝ) : State 4 := WithLp.toLp 2 ![-2 / s, 1 + 4 / s ^ 2, 0, 1]

/-- The graph in chart coordinates, `H(y) = h₁(y) w₁ + h₂(y) w₂`. -/
def manifoldH (s : ℝ) (y : State 2) : State 4 :=
  poly3 (h1L s) (y 0) (y 1) 0 • w1 s + poly3 (h2L s) (y 0) (y 1) 0 • w2 s

/-- **The order-four approximate centre manifold** `φ(x) = H(π x)` of the path. -/
def manifold (s : ℝ) (x : State 4) : State 4 := manifoldH s (critπ (bautinPathP s) x)

/-! ## The model in the critical chart -/

/-- The nonlinear part `f = F − DF(0)` of the field along the path. -/
def fnl (s : ℝ) (x : State 4) : State 4 :=
  (bautinPath s).field x - fderiv ℝ (bautinPath s).field 0 x

/-- The linear part along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fderiv_field_zero {s : ℝ} (hs : 0 < s) :
    fderiv ℝ (bautinPath s).field 0 = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      !![0, 1, 0, 0; 0, -(2 / s), -(4 + s ^ 2), 0; 0, 0, -s, 1; 1, 0, -1, -s] := by
  rw [show (bautinPath s).field = fun z => (bautinPath s).g.field (z + (bautinPath s).point)
    from rfl, fderiv_comp_add_right, zero_add, Model.fderiv_point, bautinPath_jac hs]

/-- The linear part, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_apply {s : ℝ} (hs : 0 < s) (x : State 4) (i : Fin 4) :
    fderiv ℝ (bautinPath s).field 0 x i = ![x 1, -(2 / s) * x 1 - (4 + s ^ 2) * x 2,
      -s * x 2 + x 3, x 0 - x 2 - s * x 3] i := by
  rw [fderiv_field_zero hs, Dynamics.toEuclideanCLM_apply]
  fin_cases i <;> simp [Fin.sum_univ_four] <;> ring

/-- **The nonlinearities**: `f = (0, −(4 + s²)((cos x₀ − 1) x₂ + sin x₀ · x₃), cos x₀ − 1,
sin x₀ − x₀)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fnl_apply {s : ℝ} (hs : 0 < s) (x : State 4) (i : Fin 4) :
    fnl s x i = ![0, -(4 + s ^ 2) * ((Real.cos (x 0) - 1) * x 2 + Real.sin (x 0) * x 3),
      Real.cos (x 0) - 1, Real.sin (x 0) - x 0] i := by
  have hf : (bautinPath s).field x = (bautinPath s).g.field x := by
    simp [Model.field, bautinPath_point]
  have h4 : 4 + s ^ 2 ≠ 0 := by positivity
  have hs0 : s ≠ 0 := hs.ne'
  rw [fnl, PiLp.sub_apply, hf, A_apply hs]
  fin_cases i <;>
    simp [VSM.field, bautinPath, Network.power_eq, Network.rateD, Network.rateQ, Network.X] <;>
    field_simp <;> ring

/-- The chart `ι = critι q` along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critι_bautin (s : ℝ) (y : State 2) (i : Fin 4) :
    critι (bautinPathQ s) y i = ![s * (4 + s ^ 2) * (y 0 + y 1), s * (4 + s ^ 2) * (y 0 - y 1),
      (s - 2) * y 0 + (s + 2) * y 1, (s ^ 2 + 2 - s) * y 0 + (s ^ 2 + 2 + s) * y 1] i := by
  rw [critι_apply]
  fin_cases i <;> simp [bautinPathQ, reV_apply, imV_apply, -Complex.ofReal_mul, -Complex.ofReal_pow,
    -Complex.ofReal_add, -Complex.ofReal_neg, -Complex.ofReal_sub] <;> ring

/-- The coordinates `π = critπ p` along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_bautin {s : ℝ} (hs : 0 < s) (x : State 4) :
    critπ (bautinPathP s) x 0 = PV0_0 s * x 0 + PV0_1 s * x 1 + PV0_2 s * x 2 + PV0_3 s * x 3 ∧
      critπ (bautinPathP s) x 1 =
        PV1_0 s * x 0 + PV1_1 s * x 1 + PV1_2 s * x 2 + PV1_3 s * x 3 := by
  rw [critπ_apply0, critπ_apply1, PV0_0_eq hs, PV0_1_eq hs, PV0_2_eq hs, PV0_3_eq hs,
    PV1_0_eq hs, PV1_1_eq hs, PV1_2_eq hs, PV1_3_eq hs]
  simp only [PiLp.inner_apply, Fin.sum_univ_four, reV_apply, imV_apply, RCLike.inner_apply,
    conj_trivial]
  constructor <;> ring

/-- The critical data of the path at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCritical_bautin {s : ℝ} (hs : 0 < s) :
    IsCritical (fderiv ℝ (bautinPath s).field 0) 1 (bautinPathQ s) (bautinPathP s) :=
  IsCriticalPair.isCritical (bautinPath_isCriticalPair hs) rfl

/-- `w₁ ∈ ker π`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_w1 {s : ℝ} (hs : 0 < s) :
    critπ (bautinPathP s) (w1 s) = 0 := by
  obtain ⟨h0, h1⟩ := critπ_bautin hs (w1 s)
  have e0 : critπ (bautinPathP s) (w1 s) 0 = 0 := by
    rw [h0]; simp [w1]; linear_combination piw1_0 hs
  have e1 : critπ (bautinPathP s) (w1 s) 1 = 0 := by
    rw [h1]; simp [w1]; linear_combination piw1_1 hs
  ext i; fin_cases i <;> simp [e0, e1]

/-- `w₂ ∈ ker π`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_w2 {s : ℝ} (hs : 0 < s) :
    critπ (bautinPathP s) (w2 s) = 0 := by
  obtain ⟨h0, h1⟩ := critπ_bautin hs (w2 s)
  have e0 : critπ (bautinPathP s) (w2 s) 0 = 0 := by
    rw [h0]; simp [w2]; linear_combination piw2_0 hs
  have e1 : critπ (bautinPathP s) (w2 s) 1 = 0 := by
    rw [h1]; simp [w2]; linear_combination piw2_1 hs
  ext i; fin_cases i <;> simp [e0, e1]

/-- The determinant of the first two columns of `π` does not vanish. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem DETV_ne {s : ℝ} (hs : 0 < s) : DETV s ≠ 0 := by
  have h : zeval nDETV s = -s ^ 2 := by simp only [nDETV, zeval]; push_cast; ring
  rw [DETV, h]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hs.ne')) (bval_ne_zero (bases_ne_zero hs) _)

/-- **`ker π = span(w₁, w₂)`**: a vector with `π v = 0` is `v₂ w₁ + v₃ w₂`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem ker_decomp {s : ℝ} (hs : 0 < s) {v : State 4}
    (hv : critπ (bautinPathP s) v = 0) : v = v 2 • w1 s + v 3 • w2 s := by
  set u := v - (v 2 • w1 s + v 3 • w2 s) with hud
  have hu : critπ (bautinPathP s) u = 0 := by
    simp [hud, map_sub, map_add, map_smul, hv, critπ_w1 hs, critπ_w2 hs]
  have hu2 : u 2 = 0 := by simp [hud, w1, w2]
  have hu3 : u 3 = 0 := by simp [hud, w1, w2]
  have e0 : PV0_0 s * u 0 + PV0_1 s * u 1 + PV0_2 s * u 2 + PV0_3 s * u 3 = 0 := by
    rw [← (critπ_bautin hs u).1, hu]; rfl
  have e1 : PV1_0 s * u 0 + PV1_1 s * u 1 + PV1_2 s * u 2 + PV1_3 s * u 3 = 0 := by
    rw [← (critπ_bautin hs u).2, hu]; rfl
  rw [hu2, hu3] at e0 e1
  have hD := DETV_ne hs
  have hdet := DETV_eq hs
  have hu0 : u 0 = 0 := by
    have : u 0 * DETV s = 0 := by rw [← hdet]; linear_combination PV1_1 s * e0 - PV0_1 s * e1
    exact (mul_eq_zero.mp this).resolve_right hD
  have hu1 : u 1 = 0 := by
    have : u 1 * DETV s = 0 := by rw [← hdet]; linear_combination PV0_0 s * e1 - PV1_0 s * e0
    exact (mul_eq_zero.mp this).resolve_right hD
  have hu' : u = 0 := by
    ext i; fin_cases i
    · exact hu0
    · exact hu1
    · exact hu2
    · exact hu3
  rw [hud] at hu'
  exact sub_eq_zero.mp hu'

/-- `π H(y) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_manifoldH {s : ℝ} (hs : 0 < s) (y : State 2) :
    critπ (bautinPathP s) (manifoldH s y) = 0 := by
  simp [manifoldH, map_add, map_smul, critπ_w1 hs, critπ_w2 hs]

/-! ## The manifold: the hypotheses of the reduction law -/

/-- The derivative of `H`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_manifoldH (s : ℝ) (y : State 2) :
    ∃ L : State 2 →L[ℝ] State 4, HasFDerivAt (manifoldH s) L y ∧ ∀ v, L v =
      dpoly3 (h1L s) (y 0) (y 1) 0 (v 0) (v 1) 0 • w1 s +
        dpoly3 (h2L s) (y 0) (y 1) 0 (v 0) (v 1) 0 • w2 s := by
  obtain ⟨L1, h1, hv1⟩ := Dynamics.Degenerate.hasFDerivAt_poly3 (h1L s) (Dynamics.coord 0)
    (Dynamics.coord 1) 0 y
  obtain ⟨L2, h2, hv2⟩ := Dynamics.Degenerate.hasFDerivAt_poly3 (h2L s) (Dynamics.coord 0)
    (Dynamics.coord 1) 0 y
  have e : manifoldH s = fun z => poly3 (h1L s) (Dynamics.coord 0 z) (Dynamics.coord 1 z)
      ((0 : State 2 →L[ℝ] ℝ) z) • w1 s + poly3 (h2L s) (Dynamics.coord 0 z)
        (Dynamics.coord 1 z) ((0 : State 2 →L[ℝ] ℝ) z) • w2 s := by
    funext z; simp [manifoldH]
  refine ⟨L1.smulRight (w1 s) + L2.smulRight (w2 s), ?_, fun v => ?_⟩
  · rw [e]; exact (h1.smul_const (w1 s)).add (h2.smul_const (w2 s))
  · simp [hv1, hv2]

/-- `φ` is `C¹`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem contDiffAt_manifold (s : ℝ) :
    ContDiffAt ℝ 1 (manifold s) 0 := by
  have h1 := Dynamics.Degenerate.contDiff_poly3 (h1L s)
    ((Dynamics.coord 0).comp (critπ (bautinPathP s)))
    ((Dynamics.coord 1).comp (critπ (bautinPathP s))) 0 (k := 1)
  have h2 := Dynamics.Degenerate.contDiff_poly3 (h2L s)
    ((Dynamics.coord 0).comp (critπ (bautinPathP s)))
    ((Dynamics.coord 1).comp (critπ (bautinPathP s))) 0 (k := 1)
  have e : manifold s = fun x => poly3 (h1L s) ((Dynamics.coord 0).comp (critπ (bautinPathP s)) x)
      ((Dynamics.coord 1).comp (critπ (bautinPathP s)) x) ((0 : State 4 →L[ℝ] ℝ) x) • w1 s +
      poly3 (h2L s) ((Dynamics.coord 0).comp (critπ (bautinPathP s)) x)
        ((Dynamics.coord 1).comp (critπ (bautinPathP s)) x) ((0 : State 4 →L[ℝ] ℝ) x) • w2 s := by
    funext x; simp [manifold, manifoldH]
  rw [e]
  exact ((h1.smul contDiff_const).add (h2.smul contDiff_const)).contDiffAt

/-- `φ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem manifold_zero (s : ℝ) : manifold s 0 = 0 := by
  simp [manifold, manifoldH, h1L, h2L, h1L2, h1L3, h1L4, h2L2, h2L3, h2L4]

/-- `Dφ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fderiv_manifold_zero (s : ℝ) :
    fderiv ℝ (manifold s) 0 = 0 := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_manifoldH s (critπ (bautinPathP s) 0)
  have hc : HasFDerivAt (manifold s) (L.comp (critπ (bautinPathP s))) 0 := by
    exact hL.comp (0 : State 4) ((critπ (bautinPathP s)).hasFDerivAt)
  rw [hc.fderiv]
  ext v i
  simp [hLv, h1L, h2L, h1L2, h1L3, h1L4, h2L2, h2L3, h2L4]

/-- `φ` takes values in `ker P`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critP_manifold {s : ℝ} (hs : 0 < s) (x : State 4) :
    critP (bautinPathQ s) (bautinPathP s) (manifold s x) = 0 := by
  simp [critP, manifold, critπ_manifoldH hs]

/-! ## The chart field -/

/-- The point `ι y + H(y)` of the manifold over `y`. -/
def chartPt (s : ℝ) (y : State 2) : State 4 := critι (bautinPathQ s) y + manifoldH s y

/-- **The chart field** of the manifold: `rotL 1 y + π f(ι y + H y)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem chartField_eq {s : ℝ} (hs : 0 < s) (y : State 2) :
    chartField (fderiv ℝ (bautinPath s).field 0) (fnl s) (manifold s) (critι (bautinPathQ s))
      (critπ (bautinPathP s)) y = rotL 1 y + critπ (bautinPathP s) (fnl s (chartPt s y)) := by
  have hc := isCritical_bautin hs
  rw [chartField, manifold, hc.critπ_critι, hc.apply_critι, map_add, hc.critπ_critι]
  rfl

/-- The linear part of `x₀` over `y`. -/
def lin0 (s : ℝ) (y : State 2) : ℝ := s * (4 + s ^ 2) * (y 0 + y 1)

/-- The linear part of `x₂` over `y`. -/
def lin2 (s : ℝ) (y : State 2) : ℝ := (s - 2) * y 0 + (s + 2) * y 1

/-- The linear part of `x₃` over `y`. -/
def lin3 (s : ℝ) (y : State 2) : ℝ := (s ^ 2 + 2 - s) * y 0 + (s ^ 2 + 2 + s) * y 1

/-- A planar polynomial at `y`. -/
def pv (L : List (ℝ × ℕ × ℕ × ℕ)) (y : State 2) : ℝ := poly3 L (y 0) (y 1) 0

/-- `x₀` of the manifold over `y`. -/
def ux (s : ℝ) (y : State 2) : ℝ := lin0 s y + pv (aL2 s) y + pv (aL3 s) y + pv (aL4 s) y

/-- `x₂` of the manifold over `y`. -/
def x2v (s : ℝ) (y : State 2) : ℝ := lin2 s y + pv (h1L2 s) y + pv (h1L3 s) y + pv (h1L4 s) y

/-- `x₃` of the manifold over `y`. -/
def x3v (s : ℝ) (y : State 2) : ℝ := lin3 s y + pv (h2L2 s) y + pv (h2L3 s) y + pv (h2L4 s) y

/-- `x₀ = −h₁ − (2/s) h₂` in the coefficients `CA_ij`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem x0_eq {s : ℝ} (hs : 0 < s) (y : State 2) :
    -poly3 (h1L s) (y 0) (y 1) 0 - 2 / s * poly3 (h2L s) (y 0) (y 1) 0 =
      pv (aL2 s) y + pv (aL3 s) y + pv (aL4 s) y := by
  simp only [h1L, h2L, h1L2, h1L3, h1L4, h2L2, h2L3, h2L4, aL2, aL3, aL4, pv, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append, CA_20_eq hs, CA_11_eq hs, CA_02_eq hs, CA_30_eq hs,
    CA_21_eq hs, CA_12_eq hs, CA_03_eq hs, CA_40_eq hs, CA_31_eq hs, CA_22_eq hs, CA_13_eq hs,
    CA_04_eq hs]
  ring

/-- The components `x₀`, `x₂`, `x₃` of `ι y + H(y)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem chartPt_apply {s : ℝ} (hs : 0 < s) (y : State 2) :
    chartPt s y 0 = ux s y ∧ chartPt s y 2 = x2v s y ∧ chartPt s y 3 = x3v s y := by
  have e1 : poly3 (h1L s) (y 0) (y 1) 0 = pv (h1L2 s) y + pv (h1L3 s) y + pv (h1L4 s) y := by
    simp only [h1L, PlanarFocus.Jet5.poly3_append, pv]
  have e2 : poly3 (h2L s) (y 0) (y 1) 0 = pv (h2L2 s) y + pv (h2L3 s) y + pv (h2L4 s) y := by
    simp only [h2L, PlanarFocus.Jet5.poly3_append, pv]
  have e0 := x0_eq hs y
  refine ⟨?_, ?_, ?_⟩
  · simp only [chartPt, PiLp.add_apply, critι_bautin, manifoldH, PiLp.smul_apply, smul_eq_mul, w1,
      w2, ux, lin0]
    simp
    linear_combination e0
  · simp only [chartPt, PiLp.add_apply, critι_bautin, manifoldH, PiLp.smul_apply, smul_eq_mul, w1,
      w2, x2v, lin2, e1]
    simp
    ring
  · simp only [chartPt, PiLp.add_apply, critι_bautin, manifoldH, PiLp.smul_apply, smul_eq_mul, w1,
      w2, x3v, lin3, e2]
    simp
    ring

/-- The first chart coordinate of `f` on the manifold. -/
def G0 (s : ℝ) (y : State 2) : ℝ := critπ (bautinPathP s) (fnl s (chartPt s y)) 0

/-- The second chart coordinate of `f` on the manifold. -/
def G1 (s : ℝ) (y : State 2) : ℝ := critπ (bautinPathP s) (fnl s (chartPt s y)) 1

/-- `f₁` on the manifold. -/
def f1v (s : ℝ) (y : State 2) : ℝ :=
  -(4 + s ^ 2) * ((Real.cos (ux s y) - 1) * x2v s y + Real.sin (ux s y) * x3v s y)

/-- The chart coordinates of `f` on the manifold. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem G_eq {s : ℝ} (hs : 0 < s) (y : State 2) :
    G0 s y = PV0_1 s * f1v s y + PV0_2 s * (Real.cos (ux s y) - 1) +
        PV0_3 s * (Real.sin (ux s y) - ux s y) ∧
      G1 s y = PV1_1 s * f1v s y + PV1_2 s * (Real.cos (ux s y) - 1) +
        PV1_3 s * (Real.sin (ux s y) - ux s y) := by
  obtain ⟨c0, c2, c3⟩ := chartPt_apply hs y
  obtain ⟨g0, g1⟩ := critπ_bautin hs (fnl s (chartPt s y))
  simp only [G0, G1, g0, g1, fnl_apply hs, f1v]
  simp [c0, c2, c3]

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

@[tmio M, powerlib_domain] private theorem o_l0 (s : ℝ) :
    (fun y : State 2 => lin0 s y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (lin_isBigO (s * (4 + s ^ 2)) (s * (4 + s ^ 2))).congr_left fun y => by simp only [lin0]; ring

@[tmio M, powerlib_domain] private theorem o_l2 (s : ℝ) :
    (fun y : State 2 => lin2 s y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  lin_isBigO (s - 2) (s + 2)

@[tmio M, powerlib_domain] private theorem o_l3 (s : ℝ) :
    (fun y : State 2 => lin3 s y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  lin_isBigO (s ^ 2 + 2 - s) (s ^ 2 + 2 + s)

@[tmio M, powerlib_domain] private theorem o_a2 (s : ℝ) :
    (fun y : State 2 => pv (aL2 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
  pv_isBigO _ (by simp [aL2])

@[tmio M, powerlib_domain] private theorem o_a3 (s : ℝ) :
    (fun y : State 2 => pv (aL3 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
  pv_isBigO _ (by simp [aL3])

@[tmio M, powerlib_domain] private theorem o_a4 (s : ℝ) :
    (fun y : State 2 => pv (aL4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
  pv_isBigO _ (by simp [aL4])

@[tmio M, powerlib_domain] private theorem o_b2 (s : ℝ) :
    (fun y : State 2 => pv (h1L2 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
  pv_isBigO _ (by simp [h1L2])

@[tmio M, powerlib_domain] private theorem o_b3 (s : ℝ) :
    (fun y : State 2 => pv (h1L3 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
  pv_isBigO _ (by simp [h1L3])

@[tmio M, powerlib_domain] private theorem o_b4 (s : ℝ) :
    (fun y : State 2 => pv (h1L4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
  pv_isBigO _ (by simp [h1L4])

@[tmio M, powerlib_domain] private theorem o_c2 (s : ℝ) :
    (fun y : State 2 => pv (h2L2 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
  pv_isBigO _ (by simp [h2L2])

@[tmio M, powerlib_domain] private theorem o_c3 (s : ℝ) :
    (fun y : State 2 => pv (h2L3 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
  pv_isBigO _ (by simp [h2L3])

@[tmio M, powerlib_domain] private theorem o_c4 (s : ℝ) :
    (fun y : State 2 => pv (h2L4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
  pv_isBigO _ (by simp [h2L4])

@[tmio M, powerlib_domain] private theorem o_r (s : ℝ) :
    (fun y : State 2 => pv (aL2 s) y + pv (aL3 s) y + pv (aL4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
  (((o_a2 s).add (mono (o_a3 s) (by norm_num))).add (mono (o_a4 s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_r3 (s : ℝ) :
    (fun y : State 2 => pv (aL3 s) y + pv (aL4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
  ((o_a3 s).add (mono (o_a4 s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_B (s : ℝ) :
    (fun y : State 2 => pv (h1L2 s) y + pv (h1L3 s) y + pv (h1L4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
  (((o_b2 s).add (mono (o_b3 s) (by norm_num))).add (mono (o_b4 s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_B3 (s : ℝ) :
    (fun y : State 2 => pv (h1L3 s) y + pv (h1L4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
  ((o_b3 s).add (mono (o_b4 s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_C (s : ℝ) :
    (fun y : State 2 => pv (h2L2 s) y + pv (h2L3 s) y + pv (h2L4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
  (((o_c2 s).add (mono (o_c3 s) (by norm_num))).add (mono (o_c4 s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_C3 (s : ℝ) :
    (fun y : State 2 => pv (h2L3 s) y + pv (h2L4 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
  ((o_c3 s).add (mono (o_c4 s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_u (s : ℝ) :
    (fun y : State 2 => ux s y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  ((((o_l0 s).add (mono (o_a2 s) (by norm_num))).add (mono (o_a3 s) (by norm_num))).add (mono (o_a4
    s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_X2 (s : ℝ) :
    (fun y : State 2 => x2v s y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  ((((o_l2 s).add (mono (o_b2 s) (by norm_num))).add (mono (o_b3 s) (by norm_num))).add (mono (o_b4
    s) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_X3 (s : ℝ) :
    (fun y : State 2 => x3v s y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  ((((o_l3 s).add (mono (o_c2 s) (by norm_num))).add (mono (o_c3 s) (by norm_num))).add (mono (o_c4
    s) (by norm_num)))

/-! ## The nonlinearities minus their weight-five truncations -/

/-- The weight-five truncation of `f_1`, degrees two to four . -/
def low1L4 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(T1_20 s, 2, 0, 0), (T1_11 s, 1, 1, 0), (T1_02 s, 0, 2, 0), (T1_30 s, 3, 0, 0),
   (T1_21 s, 2, 1, 0), (T1_12 s, 1, 2, 0), (T1_03 s, 0, 3, 0), (T1_40 s, 4, 0, 0),
   (T1_31 s, 3, 1, 0), (T1_22 s, 2, 2, 0), (T1_13 s, 1, 3, 0), (T1_04 s, 0, 4, 0)]

/-- The weight-five truncation of `f_1`, degree five. -/
def low1L5 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(T1_50 s, 5, 0, 0), (T1_41 s, 4, 1, 0), (T1_32 s, 3, 2, 0), (T1_23 s, 2, 3, 0),
   (T1_14 s, 1, 4, 0), (T1_05 s, 0, 5, 0)]

/-- The weight-five truncation of `f_1`. -/
def low1L (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := low1L4 s ++ low1L5 s

/-- The weight-five truncation of `f_2`, degrees two to four . -/
def low2L4 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(T2_20 s, 2, 0, 0), (T2_11 s, 1, 1, 0), (T2_02 s, 0, 2, 0), (T2_30 s, 3, 0, 0),
   (T2_21 s, 2, 1, 0), (T2_12 s, 1, 2, 0), (T2_03 s, 0, 3, 0), (T2_40 s, 4, 0, 0),
   (T2_31 s, 3, 1, 0), (T2_22 s, 2, 2, 0), (T2_13 s, 1, 3, 0), (T2_04 s, 0, 4, 0)]

/-- The weight-five truncation of `f_2`, degree five. -/
def low2L5 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(T2_50 s, 5, 0, 0), (T2_41 s, 4, 1, 0), (T2_32 s, 3, 2, 0), (T2_23 s, 2, 3, 0),
   (T2_14 s, 1, 4, 0), (T2_05 s, 0, 5, 0)]

/-- The weight-five truncation of `f_2`. -/
def low2L (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := low2L4 s ++ low2L5 s

/-- The weight-five truncation of `f_3`, degrees two to four . -/
def low3L4 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(T3_20 s, 2, 0, 0), (T3_11 s, 1, 1, 0), (T3_02 s, 0, 2, 0), (T3_30 s, 3, 0, 0),
   (T3_21 s, 2, 1, 0), (T3_12 s, 1, 2, 0), (T3_03 s, 0, 3, 0), (T3_40 s, 4, 0, 0),
   (T3_31 s, 3, 1, 0), (T3_22 s, 2, 2, 0), (T3_13 s, 1, 3, 0), (T3_04 s, 0, 4, 0)]

/-- The weight-five truncation of `f_3`, degree five. -/
def low3L5 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(T3_50 s, 5, 0, 0), (T3_41 s, 4, 1, 0), (T3_32 s, 3, 2, 0), (T3_23 s, 2, 3, 0),
   (T3_14 s, 1, 4, 0), (T3_05 s, 0, 5, 0)]

/-- The weight-five truncation of `f_3`. -/
def low3L (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := low3L4 s ++ low3L5 s

/-- The weight-five part of `−(4 + s²)((C₄(u) − 1) x₂ + S₅(u) x₃)` in the pieces of `u`, `x₂`, `x₃`
(`C₄`, `S₅` the Taylor polynomials of `cos`, `sin`). -/
def lowF1 (s l0 a2 a3 a4 l2 b2 b3 l3 c2 c3 c4 : ℝ) : ℝ :=
  -(4 + s ^ 2) * (-((l0 ^ 2 + 2 * l0 * a2 + 2 * l0 * a3 + a2 ^ 2) * l2 +
    (l0 ^ 2 + 2 * l0 * a2) * b2 + l0 ^ 2 * b3) / 2 + l0 ^ 4 * l2 / 24 +
    (l0 * l3 + l0 * c2 + a2 * l3 + l0 * c3 + a2 * c2 + a3 * l3 + l0 * c4 + a2 * c3 + a3 * c2 +
      a4 * l3) - ((l0 ^ 3 + 3 * l0 ^ 2 * a2) * l3 + l0 ^ 3 * c2) / 6)

/-- The weight-five part of `C₄(u) − 1`. -/
def lowF2 (l0 a2 a3 a4 : ℝ) : ℝ :=
  -(l0 ^ 2 + 2 * l0 * a2 + 2 * l0 * a3 + 2 * l0 * a4 + a2 ^ 2 + 2 * a2 * a3) / 2 +
    (l0 ^ 4 + 4 * l0 ^ 3 * a2) / 24

/-- The weight-five part of `S₅(u) − u`. -/
def lowF3 (l0 a2 a3 : ℝ) : ℝ :=
  -(l0 ^ 3 + 3 * l0 ^ 2 * a2 + 3 * l0 ^ 2 * a3 + 3 * l0 * a2 ^ 2) / 6 + l0 ^ 5 / 120

/-- The product `l0 · l0 · l2` of pieces as a planar polynomial. -/
def pE_l0_l0_l2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_l2_30 s, 3, 0, 0), (Sl0_l0_l2_21 s, 2, 1, 0), (Sl0_l0_l2_12 s, 1, 2, 0),
   (Sl0_l0_l2_03 s, 0, 3, 0)]

/-- The product `l0 · l0 · l2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_l0_l0_l2_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y * lin2 s y = pv (pE_l0_l0_l2 s) y := by
  simp only [lin0, lin2, pv, pE_l0_l0_l2, Sl0_l0_l2_30, Sl0_l0_l2_21, Sl0_l0_l2_12, Sl0_l0_l2_03,
    poly3_cons, poly3_nil]
  ring

/-- The product `a2 · l0 · l2` of pieces as a planar polynomial. -/
def pE_a2_l0_l2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_l0_l2_40 s, 4, 0, 0), (Sa2_l0_l2_31 s, 3, 1, 0), (Sa2_l0_l2_22 s, 2, 2, 0),
   (Sa2_l0_l2_13 s, 1, 3, 0), (Sa2_l0_l2_04 s, 0, 4, 0)]

/-- The product `a2 · l0 · l2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_l0_l2_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * lin0 s y * lin2 s y = pv (pE_a2_l0_l2 s) y := by
  simp only [lin0, lin2, pv, pE_a2_l0_l2, aL2, Sa2_l0_l2_40, Sa2_l0_l2_31, Sa2_l0_l2_22,
    Sa2_l0_l2_13, Sa2_l0_l2_04, poly3_cons, poly3_nil]
  ring

/-- The product `a3 · l0 · l2` of pieces as a planar polynomial. -/
def pE_a3_l0_l2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa3_l0_l2_50 s, 5, 0, 0), (Sa3_l0_l2_41 s, 4, 1, 0), (Sa3_l0_l2_32 s, 3, 2, 0),
   (Sa3_l0_l2_23 s, 2, 3, 0), (Sa3_l0_l2_14 s, 1, 4, 0), (Sa3_l0_l2_05 s, 0, 5, 0)]

/-- The product `a3 · l0 · l2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a3_l0_l2_eq (s : ℝ) (y : State 2) :
    pv (aL3 s) y * lin0 s y * lin2 s y = pv (pE_a3_l0_l2 s) y := by
  simp only [lin0, lin2, pv, pE_a3_l0_l2, aL3, Sa3_l0_l2_50, Sa3_l0_l2_41, Sa3_l0_l2_32,
    Sa3_l0_l2_23, Sa3_l0_l2_14, Sa3_l0_l2_05, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · a2 · l2` of pieces as a planar polynomial. -/
def pE_a2_a2_l2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_a2_l2_50 s, 5, 0, 0), (Sa2_a2_l2_41 s, 4, 1, 0), (Sa2_a2_l2_32 s, 3, 2, 0),
   (Sa2_a2_l2_23 s, 2, 3, 0), (Sa2_a2_l2_14 s, 1, 4, 0), (Sa2_a2_l2_05 s, 0, 5, 0)]

/-- The product `a2 · a2 · l2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_a2_l2_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (aL2 s) y * lin2 s y = pv (pE_a2_a2_l2 s) y := by
  simp only [lin2, pv, pE_a2_a2_l2, aL2, Sa2_a2_l2_50, Sa2_a2_l2_41, Sa2_a2_l2_32, Sa2_a2_l2_23,
    Sa2_a2_l2_14, Sa2_a2_l2_05, poly3_cons, poly3_nil]
  ring

/-- The product `b2 · l0 · l0` of pieces as a planar polynomial. -/
def pE_b2_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sb2_l0_l0_40 s, 4, 0, 0), (Sb2_l0_l0_31 s, 3, 1, 0), (Sb2_l0_l0_22 s, 2, 2, 0),
   (Sb2_l0_l0_13 s, 1, 3, 0), (Sb2_l0_l0_04 s, 0, 4, 0)]

/-- The product `b2 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_b2_l0_l0_eq (s : ℝ) (y : State 2) :
    pv (h1L2 s) y * lin0 s y * lin0 s y = pv (pE_b2_l0_l0 s) y := by
  simp only [lin0, pv, pE_b2_l0_l0, h1L2, Sb2_l0_l0_40, Sb2_l0_l0_31, Sb2_l0_l0_22, Sb2_l0_l0_13,
    Sb2_l0_l0_04, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · b2 · l0` of pieces as a planar polynomial. -/
def pE_a2_b2_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_b2_l0_50 s, 5, 0, 0), (Sa2_b2_l0_41 s, 4, 1, 0), (Sa2_b2_l0_32 s, 3, 2, 0),
   (Sa2_b2_l0_23 s, 2, 3, 0), (Sa2_b2_l0_14 s, 1, 4, 0), (Sa2_b2_l0_05 s, 0, 5, 0)]

/-- The product `a2 · b2 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_b2_l0_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (h1L2 s) y * lin0 s y = pv (pE_a2_b2_l0 s) y := by
  simp only [lin0, pv, pE_a2_b2_l0, aL2, h1L2, Sa2_b2_l0_50, Sa2_b2_l0_41, Sa2_b2_l0_32,
    Sa2_b2_l0_23, Sa2_b2_l0_14, Sa2_b2_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `b3 · l0 · l0` of pieces as a planar polynomial. -/
def pE_b3_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sb3_l0_l0_50 s, 5, 0, 0), (Sb3_l0_l0_41 s, 4, 1, 0), (Sb3_l0_l0_32 s, 3, 2, 0),
   (Sb3_l0_l0_23 s, 2, 3, 0), (Sb3_l0_l0_14 s, 1, 4, 0), (Sb3_l0_l0_05 s, 0, 5, 0)]

/-- The product `b3 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_b3_l0_l0_eq (s : ℝ) (y : State 2) :
    pv (h1L3 s) y * lin0 s y * lin0 s y = pv (pE_b3_l0_l0 s) y := by
  simp only [lin0, pv, pE_b3_l0_l0, h1L3, Sb3_l0_l0_50, Sb3_l0_l0_41, Sb3_l0_l0_32, Sb3_l0_l0_23,
    Sb3_l0_l0_14, Sb3_l0_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `l0 · l0 · l0 · l0 · l2` of pieces as a planar polynomial. -/
def pE_l0_l0_l0_l0_l2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_l0_l0_l2_50 s, 5, 0, 0), (Sl0_l0_l0_l0_l2_41 s, 4, 1, 0),
   (Sl0_l0_l0_l0_l2_32 s, 3, 2, 0), (Sl0_l0_l0_l0_l2_23 s, 2, 3, 0),
   (Sl0_l0_l0_l0_l2_14 s, 1, 4, 0), (Sl0_l0_l0_l0_l2_05 s, 0, 5, 0)]

/-- The product `l0 · l0 · l0 · l0 · l2` of pieces in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem pE_l0_l0_l0_l0_l2_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y * lin0 s y * lin0 s y * lin2 s y = pv (pE_l0_l0_l0_l0_l2 s) y := by
  simp only [lin0, lin2, pv, pE_l0_l0_l0_l0_l2, Sl0_l0_l0_l0_l2_50, Sl0_l0_l0_l0_l2_41,
    Sl0_l0_l0_l0_l2_32, Sl0_l0_l0_l0_l2_23, Sl0_l0_l0_l0_l2_14, Sl0_l0_l0_l0_l2_05, poly3_cons,
    poly3_nil]
  ring

/-- The product `l0 · l3` of pieces as a planar polynomial. -/
def pE_l0_l3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l3_20 s, 2, 0, 0), (Sl0_l3_11 s, 1, 1, 0), (Sl0_l3_02 s, 0, 2, 0)]

/-- The product `l0 · l3` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_l0_l3_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin3 s y = pv (pE_l0_l3 s) y := by
  simp only [lin0, lin3, pv, pE_l0_l3, Sl0_l3_20, Sl0_l3_11, Sl0_l3_02, poly3_cons, poly3_nil]
  ring

/-- The product `c2 · l0` of pieces as a planar polynomial. -/
def pE_c2_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sc2_l0_30 s, 3, 0, 0), (Sc2_l0_21 s, 2, 1, 0), (Sc2_l0_12 s, 1, 2, 0), (Sc2_l0_03 s, 0, 3, 0)]

/-- The product `c2 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_c2_l0_eq (s : ℝ) (y : State 2) :
    pv (h2L2 s) y * lin0 s y = pv (pE_c2_l0 s) y := by
  simp only [lin0, pv, pE_c2_l0, h2L2, Sc2_l0_30, Sc2_l0_21, Sc2_l0_12, Sc2_l0_03, poly3_cons,
    poly3_nil]
  ring

/-- The product `a2 · l3` of pieces as a planar polynomial. -/
def pE_a2_l3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_l3_30 s, 3, 0, 0), (Sa2_l3_21 s, 2, 1, 0), (Sa2_l3_12 s, 1, 2, 0), (Sa2_l3_03 s, 0, 3, 0)]

/-- The product `a2 · l3` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_l3_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * lin3 s y = pv (pE_a2_l3 s) y := by
  simp only [lin3, pv, pE_a2_l3, aL2, Sa2_l3_30, Sa2_l3_21, Sa2_l3_12, Sa2_l3_03, poly3_cons,
    poly3_nil]
  ring

/-- The product `c3 · l0` of pieces as a planar polynomial. -/
def pE_c3_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sc3_l0_40 s, 4, 0, 0), (Sc3_l0_31 s, 3, 1, 0), (Sc3_l0_22 s, 2, 2, 0), (Sc3_l0_13 s, 1, 3, 0),
   (Sc3_l0_04 s, 0, 4, 0)]

/-- The product `c3 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_c3_l0_eq (s : ℝ) (y : State 2) :
    pv (h2L3 s) y * lin0 s y = pv (pE_c3_l0 s) y := by
  simp only [lin0, pv, pE_c3_l0, h2L3, Sc3_l0_40, Sc3_l0_31, Sc3_l0_22, Sc3_l0_13, Sc3_l0_04,
    poly3_cons, poly3_nil]
  ring

/-- The product `a2 · c2` of pieces as a planar polynomial. -/
def pE_a2_c2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_c2_40 s, 4, 0, 0), (Sa2_c2_31 s, 3, 1, 0), (Sa2_c2_22 s, 2, 2, 0), (Sa2_c2_13 s, 1, 3, 0),
   (Sa2_c2_04 s, 0, 4, 0)]

/-- The product `a2 · c2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_c2_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (h2L2 s) y = pv (pE_a2_c2 s) y := by
  simp only [pv, pE_a2_c2, aL2, h2L2, Sa2_c2_40, Sa2_c2_31, Sa2_c2_22, Sa2_c2_13, Sa2_c2_04,
    poly3_cons, poly3_nil]
  ring

/-- The product `a3 · l3` of pieces as a planar polynomial. -/
def pE_a3_l3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa3_l3_40 s, 4, 0, 0), (Sa3_l3_31 s, 3, 1, 0), (Sa3_l3_22 s, 2, 2, 0), (Sa3_l3_13 s, 1, 3, 0),
   (Sa3_l3_04 s, 0, 4, 0)]

/-- The product `a3 · l3` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a3_l3_eq (s : ℝ) (y : State 2) :
    pv (aL3 s) y * lin3 s y = pv (pE_a3_l3 s) y := by
  simp only [lin3, pv, pE_a3_l3, aL3, Sa3_l3_40, Sa3_l3_31, Sa3_l3_22, Sa3_l3_13, Sa3_l3_04,
    poly3_cons, poly3_nil]
  ring

/-- The product `c4 · l0` of pieces as a planar polynomial. -/
def pE_c4_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sc4_l0_50 s, 5, 0, 0), (Sc4_l0_41 s, 4, 1, 0), (Sc4_l0_32 s, 3, 2, 0), (Sc4_l0_23 s, 2, 3, 0),
   (Sc4_l0_14 s, 1, 4, 0), (Sc4_l0_05 s, 0, 5, 0)]

/-- The product `c4 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_c4_l0_eq (s : ℝ) (y : State 2) :
    pv (h2L4 s) y * lin0 s y = pv (pE_c4_l0 s) y := by
  simp only [lin0, pv, pE_c4_l0, h2L4, Sc4_l0_50, Sc4_l0_41, Sc4_l0_32, Sc4_l0_23, Sc4_l0_14,
    Sc4_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · c3` of pieces as a planar polynomial. -/
def pE_a2_c3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_c3_50 s, 5, 0, 0), (Sa2_c3_41 s, 4, 1, 0), (Sa2_c3_32 s, 3, 2, 0), (Sa2_c3_23 s, 2, 3, 0),
   (Sa2_c3_14 s, 1, 4, 0), (Sa2_c3_05 s, 0, 5, 0)]

/-- The product `a2 · c3` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_c3_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (h2L3 s) y = pv (pE_a2_c3 s) y := by
  simp only [pv, pE_a2_c3, aL2, h2L3, Sa2_c3_50, Sa2_c3_41, Sa2_c3_32, Sa2_c3_23, Sa2_c3_14,
    Sa2_c3_05, poly3_cons, poly3_nil]
  ring

/-- The product `a3 · c2` of pieces as a planar polynomial. -/
def pE_a3_c2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa3_c2_50 s, 5, 0, 0), (Sa3_c2_41 s, 4, 1, 0), (Sa3_c2_32 s, 3, 2, 0), (Sa3_c2_23 s, 2, 3, 0),
   (Sa3_c2_14 s, 1, 4, 0), (Sa3_c2_05 s, 0, 5, 0)]

/-- The product `a3 · c2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a3_c2_eq (s : ℝ) (y : State 2) :
    pv (aL3 s) y * pv (h2L2 s) y = pv (pE_a3_c2 s) y := by
  simp only [pv, pE_a3_c2, aL3, h2L2, Sa3_c2_50, Sa3_c2_41, Sa3_c2_32, Sa3_c2_23, Sa3_c2_14,
    Sa3_c2_05, poly3_cons, poly3_nil]
  ring

/-- The product `a4 · l3` of pieces as a planar polynomial. -/
def pE_a4_l3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa4_l3_50 s, 5, 0, 0), (Sa4_l3_41 s, 4, 1, 0), (Sa4_l3_32 s, 3, 2, 0), (Sa4_l3_23 s, 2, 3, 0),
   (Sa4_l3_14 s, 1, 4, 0), (Sa4_l3_05 s, 0, 5, 0)]

/-- The product `a4 · l3` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a4_l3_eq (s : ℝ) (y : State 2) :
    pv (aL4 s) y * lin3 s y = pv (pE_a4_l3 s) y := by
  simp only [lin3, pv, pE_a4_l3, aL4, Sa4_l3_50, Sa4_l3_41, Sa4_l3_32, Sa4_l3_23, Sa4_l3_14,
    Sa4_l3_05, poly3_cons, poly3_nil]
  ring

/-- The product `l0 · l0 · l0 · l3` of pieces as a planar polynomial. -/
def pE_l0_l0_l0_l3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_l0_l3_40 s, 4, 0, 0), (Sl0_l0_l0_l3_31 s, 3, 1, 0), (Sl0_l0_l0_l3_22 s, 2, 2, 0),
   (Sl0_l0_l0_l3_13 s, 1, 3, 0), (Sl0_l0_l0_l3_04 s, 0, 4, 0)]

/-- The product `l0 · l0 · l0 · l3` of pieces in the monomials of `y`. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem pE_l0_l0_l0_l3_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y * lin0 s y * lin3 s y = pv (pE_l0_l0_l0_l3 s) y := by
  simp only [lin0, lin3, pv, pE_l0_l0_l0_l3, Sl0_l0_l0_l3_40, Sl0_l0_l0_l3_31, Sl0_l0_l0_l3_22,
    Sl0_l0_l0_l3_13, Sl0_l0_l0_l3_04, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · l0 · l0 · l3` of pieces as a planar polynomial. -/
def pE_a2_l0_l0_l3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_l0_l0_l3_50 s, 5, 0, 0), (Sa2_l0_l0_l3_41 s, 4, 1, 0), (Sa2_l0_l0_l3_32 s, 3, 2, 0),
   (Sa2_l0_l0_l3_23 s, 2, 3, 0), (Sa2_l0_l0_l3_14 s, 1, 4, 0), (Sa2_l0_l0_l3_05 s, 0, 5, 0)]

/-- The product `a2 · l0 · l0 · l3` of pieces in the monomials of `y`. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem pE_a2_l0_l0_l3_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * lin0 s y * lin0 s y * lin3 s y = pv (pE_a2_l0_l0_l3 s) y := by
  simp only [lin0, lin3, pv, pE_a2_l0_l0_l3, aL2, Sa2_l0_l0_l3_50, Sa2_l0_l0_l3_41, Sa2_l0_l0_l3_32,
    Sa2_l0_l0_l3_23, Sa2_l0_l0_l3_14, Sa2_l0_l0_l3_05, poly3_cons, poly3_nil]
  ring

/-- The product `c2 · l0 · l0 · l0` of pieces as a planar polynomial. -/
def pE_c2_l0_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sc2_l0_l0_l0_50 s, 5, 0, 0), (Sc2_l0_l0_l0_41 s, 4, 1, 0), (Sc2_l0_l0_l0_32 s, 3, 2, 0),
   (Sc2_l0_l0_l0_23 s, 2, 3, 0), (Sc2_l0_l0_l0_14 s, 1, 4, 0), (Sc2_l0_l0_l0_05 s, 0, 5, 0)]

/-- The product `c2 · l0 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem pE_c2_l0_l0_l0_eq (s : ℝ) (y : State 2) :
    pv (h2L2 s) y * lin0 s y * lin0 s y * lin0 s y = pv (pE_c2_l0_l0_l0 s) y := by
  simp only [lin0, pv, pE_c2_l0_l0_l0, h2L2, Sc2_l0_l0_l0_50, Sc2_l0_l0_l0_41, Sc2_l0_l0_l0_32,
    Sc2_l0_l0_l0_23, Sc2_l0_l0_l0_14, Sc2_l0_l0_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `l0 · l0` of pieces as a planar polynomial. -/
def pE_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_20 s, 2, 0, 0), (Sl0_l0_11 s, 1, 1, 0), (Sl0_l0_02 s, 0, 2, 0)]

/-- The product `l0 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_l0_l0_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y = pv (pE_l0_l0 s) y := by
  simp only [lin0, pv, pE_l0_l0, Sl0_l0_20, Sl0_l0_11, Sl0_l0_02, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · l0` of pieces as a planar polynomial. -/
def pE_a2_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_l0_30 s, 3, 0, 0), (Sa2_l0_21 s, 2, 1, 0), (Sa2_l0_12 s, 1, 2, 0), (Sa2_l0_03 s, 0, 3, 0)]

/-- The product `a2 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_l0_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * lin0 s y = pv (pE_a2_l0 s) y := by
  simp only [lin0, pv, pE_a2_l0, aL2, Sa2_l0_30, Sa2_l0_21, Sa2_l0_12, Sa2_l0_03, poly3_cons,
    poly3_nil]
  ring

/-- The product `a3 · l0` of pieces as a planar polynomial. -/
def pE_a3_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa3_l0_40 s, 4, 0, 0), (Sa3_l0_31 s, 3, 1, 0), (Sa3_l0_22 s, 2, 2, 0), (Sa3_l0_13 s, 1, 3, 0),
   (Sa3_l0_04 s, 0, 4, 0)]

/-- The product `a3 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a3_l0_eq (s : ℝ) (y : State 2) :
    pv (aL3 s) y * lin0 s y = pv (pE_a3_l0 s) y := by
  simp only [lin0, pv, pE_a3_l0, aL3, Sa3_l0_40, Sa3_l0_31, Sa3_l0_22, Sa3_l0_13, Sa3_l0_04,
    poly3_cons, poly3_nil]
  ring

/-- The product `a4 · l0` of pieces as a planar polynomial. -/
def pE_a4_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa4_l0_50 s, 5, 0, 0), (Sa4_l0_41 s, 4, 1, 0), (Sa4_l0_32 s, 3, 2, 0), (Sa4_l0_23 s, 2, 3, 0),
   (Sa4_l0_14 s, 1, 4, 0), (Sa4_l0_05 s, 0, 5, 0)]

/-- The product `a4 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a4_l0_eq (s : ℝ) (y : State 2) :
    pv (aL4 s) y * lin0 s y = pv (pE_a4_l0 s) y := by
  simp only [lin0, pv, pE_a4_l0, aL4, Sa4_l0_50, Sa4_l0_41, Sa4_l0_32, Sa4_l0_23, Sa4_l0_14,
    Sa4_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · a2` of pieces as a planar polynomial. -/
def pE_a2_a2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_a2_40 s, 4, 0, 0), (Sa2_a2_31 s, 3, 1, 0), (Sa2_a2_22 s, 2, 2, 0), (Sa2_a2_13 s, 1, 3, 0),
   (Sa2_a2_04 s, 0, 4, 0)]

/-- The product `a2 · a2` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_a2_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (aL2 s) y = pv (pE_a2_a2 s) y := by
  simp only [pv, pE_a2_a2, aL2, Sa2_a2_40, Sa2_a2_31, Sa2_a2_22, Sa2_a2_13, Sa2_a2_04, poly3_cons,
    poly3_nil]
  ring

/-- The product `a2 · a3` of pieces as a planar polynomial. -/
def pE_a2_a3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_a3_50 s, 5, 0, 0), (Sa2_a3_41 s, 4, 1, 0), (Sa2_a3_32 s, 3, 2, 0), (Sa2_a3_23 s, 2, 3, 0),
   (Sa2_a3_14 s, 1, 4, 0), (Sa2_a3_05 s, 0, 5, 0)]

/-- The product `a2 · a3` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_a3_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (aL3 s) y = pv (pE_a2_a3 s) y := by
  simp only [pv, pE_a2_a3, aL2, aL3, Sa2_a3_50, Sa2_a3_41, Sa2_a3_32, Sa2_a3_23, Sa2_a3_14,
    Sa2_a3_05, poly3_cons, poly3_nil]
  ring

/-- The product `l0 · l0 · l0 · l0` of pieces as a planar polynomial. -/
def pE_l0_l0_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_l0_l0_40 s, 4, 0, 0), (Sl0_l0_l0_l0_31 s, 3, 1, 0), (Sl0_l0_l0_l0_22 s, 2, 2, 0),
   (Sl0_l0_l0_l0_13 s, 1, 3, 0), (Sl0_l0_l0_l0_04 s, 0, 4, 0)]

/-- The product `l0 · l0 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem pE_l0_l0_l0_l0_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y * lin0 s y * lin0 s y = pv (pE_l0_l0_l0_l0 s) y := by
  simp only [lin0, pv, pE_l0_l0_l0_l0, Sl0_l0_l0_l0_40, Sl0_l0_l0_l0_31, Sl0_l0_l0_l0_22,
    Sl0_l0_l0_l0_13, Sl0_l0_l0_l0_04, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · l0 · l0 · l0` of pieces as a planar polynomial. -/
def pE_a2_l0_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_l0_l0_l0_50 s, 5, 0, 0), (Sa2_l0_l0_l0_41 s, 4, 1, 0), (Sa2_l0_l0_l0_32 s, 3, 2, 0),
   (Sa2_l0_l0_l0_23 s, 2, 3, 0), (Sa2_l0_l0_l0_14 s, 1, 4, 0), (Sa2_l0_l0_l0_05 s, 0, 5, 0)]

/-- The product `a2 · l0 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem pE_a2_l0_l0_l0_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * lin0 s y * lin0 s y * lin0 s y = pv (pE_a2_l0_l0_l0 s) y := by
  simp only [lin0, pv, pE_a2_l0_l0_l0, aL2, Sa2_l0_l0_l0_50, Sa2_l0_l0_l0_41, Sa2_l0_l0_l0_32,
    Sa2_l0_l0_l0_23, Sa2_l0_l0_l0_14, Sa2_l0_l0_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `l0 · l0 · l0` of pieces as a planar polynomial. -/
def pE_l0_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_l0_30 s, 3, 0, 0), (Sl0_l0_l0_21 s, 2, 1, 0), (Sl0_l0_l0_12 s, 1, 2, 0),
   (Sl0_l0_l0_03 s, 0, 3, 0)]

/-- The product `l0 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_l0_l0_l0_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y * lin0 s y = pv (pE_l0_l0_l0 s) y := by
  simp only [lin0, pv, pE_l0_l0_l0, Sl0_l0_l0_30, Sl0_l0_l0_21, Sl0_l0_l0_12, Sl0_l0_l0_03,
    poly3_cons, poly3_nil]
  ring

/-- The product `a2 · l0 · l0` of pieces as a planar polynomial. -/
def pE_a2_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_l0_l0_40 s, 4, 0, 0), (Sa2_l0_l0_31 s, 3, 1, 0), (Sa2_l0_l0_22 s, 2, 2, 0),
   (Sa2_l0_l0_13 s, 1, 3, 0), (Sa2_l0_l0_04 s, 0, 4, 0)]

/-- The product `a2 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_l0_l0_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * lin0 s y * lin0 s y = pv (pE_a2_l0_l0 s) y := by
  simp only [lin0, pv, pE_a2_l0_l0, aL2, Sa2_l0_l0_40, Sa2_l0_l0_31, Sa2_l0_l0_22, Sa2_l0_l0_13,
    Sa2_l0_l0_04, poly3_cons, poly3_nil]
  ring

/-- The product `a3 · l0 · l0` of pieces as a planar polynomial. -/
def pE_a3_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa3_l0_l0_50 s, 5, 0, 0), (Sa3_l0_l0_41 s, 4, 1, 0), (Sa3_l0_l0_32 s, 3, 2, 0),
   (Sa3_l0_l0_23 s, 2, 3, 0), (Sa3_l0_l0_14 s, 1, 4, 0), (Sa3_l0_l0_05 s, 0, 5, 0)]

/-- The product `a3 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a3_l0_l0_eq (s : ℝ) (y : State 2) :
    pv (aL3 s) y * lin0 s y * lin0 s y = pv (pE_a3_l0_l0 s) y := by
  simp only [lin0, pv, pE_a3_l0_l0, aL3, Sa3_l0_l0_50, Sa3_l0_l0_41, Sa3_l0_l0_32, Sa3_l0_l0_23,
    Sa3_l0_l0_14, Sa3_l0_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `a2 · a2 · l0` of pieces as a planar polynomial. -/
def pE_a2_a2_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sa2_a2_l0_50 s, 5, 0, 0), (Sa2_a2_l0_41 s, 4, 1, 0), (Sa2_a2_l0_32 s, 3, 2, 0),
   (Sa2_a2_l0_23 s, 2, 3, 0), (Sa2_a2_l0_14 s, 1, 4, 0), (Sa2_a2_l0_05 s, 0, 5, 0)]

/-- The product `a2 · a2 · l0` of pieces in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pE_a2_a2_l0_eq (s : ℝ) (y : State 2) :
    pv (aL2 s) y * pv (aL2 s) y * lin0 s y = pv (pE_a2_a2_l0 s) y := by
  simp only [lin0, pv, pE_a2_a2_l0, aL2, Sa2_a2_l0_50, Sa2_a2_l0_41, Sa2_a2_l0_32, Sa2_a2_l0_23,
    Sa2_a2_l0_14, Sa2_a2_l0_05, poly3_cons, poly3_nil]
  ring

/-- The product `l0 · l0 · l0 · l0 · l0` of pieces as a planar polynomial. -/
def pE_l0_l0_l0_l0_l0 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(Sl0_l0_l0_l0_l0_50 s, 5, 0, 0), (Sl0_l0_l0_l0_l0_41 s, 4, 1, 0),
   (Sl0_l0_l0_l0_l0_32 s, 3, 2, 0), (Sl0_l0_l0_l0_l0_23 s, 2, 3, 0),
   (Sl0_l0_l0_l0_l0_14 s, 1, 4, 0), (Sl0_l0_l0_l0_l0_05 s, 0, 5, 0)]

/-- The product `l0 · l0 · l0 · l0 · l0` of pieces in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem pE_l0_l0_l0_l0_l0_eq (s : ℝ) (y : State 2) :
    lin0 s y * lin0 s y * lin0 s y * lin0 s y * lin0 s y = pv (pE_l0_l0_l0_l0_l0 s) y := by
  simp only [lin0, pv, pE_l0_l0_l0_l0_l0, Sl0_l0_l0_l0_l0_50, Sl0_l0_l0_l0_l0_41,
    Sl0_l0_l0_l0_l0_32, Sl0_l0_l0_l0_l0_23, Sl0_l0_l0_l0_l0_14, Sl0_l0_l0_l0_l0_05, poly3_cons,
    poly3_nil]
  ring

/-- The weight-five truncation of `f_1` in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem low1_eq (s : ℝ) (y : State 2) :
    lowF1 s (lin0 s y) (pv (aL2 s) y) (pv (aL3 s) y) (pv (aL4 s) y) (lin2 s y) (pv (h1L2 s) y) (pv
    (h1L3 s) y) (lin3 s y) (pv (h2L2 s) y) (pv (h2L3 s) y) (pv (h2L4 s) y) = pv (low1L s) y := by
  have e : lowF1 s (lin0 s y) (pv (aL2 s) y) (pv (aL3 s) y) (pv (aL4 s) y) (lin2 s y) (pv (h1L2 s)
      y) (pv (h1L3 s) y) (lin3 s y) (pv (h2L2 s) y) (pv (h2L3 s) y) (pv (h2L4 s) y) = (2 + (s ^ 2) /
      (2)) * (lin0 s y * lin0 s y * lin2 s y) + (4 + s ^ 2) * (pv (aL2 s) y * lin0 s y * lin2 s y) +
      (4 + s ^ 2) * (pv (aL3 s) y * lin0 s y * lin2 s y) + (2 + (s ^ 2) / (2)) * (pv (aL2 s) y * pv
      (aL2 s) y * lin2 s y) + (2 + (s ^ 2) / (2)) * (pv (h1L2 s) y * lin0 s y * lin0 s y) + (4 + s ^
      2) * (pv (aL2 s) y * pv (h1L2 s) y * lin0 s y) + (2 + (s ^ 2) / (2)) * (pv (h1L3 s) y * lin0 s
      y * lin0 s y) + ((-1 / 6) + (-s ^ 2) / (24)) * (lin0 s y * lin0 s y * lin0 s y * lin0 s y *
      lin2 s y) + (-4 - s ^ 2) * (lin0 s y * lin3 s y) + (-4 - s ^ 2) * (pv (h2L2 s) y * lin0 s y) +
      (-4 - s ^ 2) * (pv (aL2 s) y * lin3 s y) + (-4 - s ^ 2) * (pv (h2L3 s) y * lin0 s y) + (-4 - s
      ^ 2) * (pv (aL2 s) y * pv (h2L2 s) y) + (-4 - s ^ 2) * (pv (aL3 s) y * lin3 s y) + (-4 - s ^
      2) * (pv (h2L4 s) y * lin0 s y) + (-4 - s ^ 2) * (pv (aL2 s) y * pv (h2L3 s) y) + (-4 - s ^ 2)
      * (pv (aL3 s) y * pv (h2L2 s) y) + (-4 - s ^ 2) * (pv (aL4 s) y * lin3 s y) + ((2 / 3) + (s ^
      2) / (6)) * (lin0 s y * lin0 s y * lin0 s y * lin3 s y) + (2 + (s ^ 2) / (2)) * (pv (aL2 s) y
      * lin0 s y * lin0 s y * lin3 s y) + ((2 / 3) + (s ^ 2) / (6)) * (pv (h2L2 s) y * lin0 s y *
      lin0 s y * lin0 s y) := by
    simp only [lowF1]; ring
  rw [e, pE_l0_l0_l0_l0_l2_eq s y, pE_l0_l0_l0_l3_eq s y, pE_a2_l0_l0_l3_eq s y, pE_c2_l0_l0_l0_eq s
    y, pE_l0_l0_l2_eq s y, pE_a2_l0_l2_eq s y, pE_a3_l0_l2_eq s y, pE_a2_a2_l2_eq s y,
    pE_b2_l0_l0_eq s y, pE_a2_b2_l0_eq s y, pE_b3_l0_l0_eq s y, pE_l0_l3_eq s y, pE_c2_l0_eq s y,
    pE_a2_l3_eq s y, pE_c3_l0_eq s y, pE_a2_c2_eq s y, pE_a3_l3_eq s y, pE_c4_l0_eq s y, pE_a2_c3_eq
    s y, pE_a3_c2_eq s y, pE_a4_l3_eq s y]
  simp only [pv, low1L, low1L4, low1L5, pE_l0_l0_l2, pE_a2_l0_l2, pE_a3_l0_l2, pE_a2_a2_l2,
    pE_b2_l0_l0, pE_a2_b2_l0, pE_b3_l0_l0, pE_l0_l0_l0_l0_l2, pE_l0_l3, pE_c2_l0, pE_a2_l3,
    pE_c3_l0, pE_a2_c2, pE_a3_l3, pE_c4_l0, pE_a2_c3, pE_a3_c2, pE_a4_l3, pE_l0_l0_l0_l3,
    pE_a2_l0_l0_l3, pE_c2_l0_l0_l0, T1_20, T1_11, T1_02, T1_30, T1_21, T1_12, T1_03, T1_40, T1_31,
    T1_22, T1_13, T1_04, T1_50, T1_41, T1_32, T1_23, T1_14, T1_05, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `f_2` in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem low2_eq (s : ℝ) (y : State 2) :
    lowF2 (lin0 s y) (pv (aL2 s) y) (pv (aL3 s) y) (pv (aL4 s) y) = pv (low2L s) y := by
  have e : lowF2 (lin0 s y) (pv (aL2 s) y) (pv (aL3 s) y) (pv (aL4 s) y) = ((-1 / 2)) * (lin0 s y *
      lin0 s y) + (-1) * (pv (aL2 s) y * lin0 s y) + (-1) * (pv (aL3 s) y * lin0 s y) + (-1) * (pv
      (aL4 s) y * lin0 s y) + ((-1 / 2)) * (pv (aL2 s) y * pv (aL2 s) y) + (-1) * (pv (aL2 s) y * pv
      (aL3 s) y) + ((1 / 24)) * (lin0 s y * lin0 s y * lin0 s y * lin0 s y) + ((1 / 6)) * (pv (aL2
      s) y * lin0 s y * lin0 s y * lin0 s y) := by
    simp only [lowF2]; ring
  rw [e, pE_l0_l0_l0_l0_eq s y, pE_a2_l0_l0_l0_eq s y, pE_l0_l0_eq s y, pE_a2_l0_eq s y, pE_a3_l0_eq
    s y, pE_a4_l0_eq s y, pE_a2_a2_eq s y, pE_a2_a3_eq s y]
  simp only [pv, low2L, low2L4, low2L5, pE_l0_l0, pE_a2_l0, pE_a3_l0, pE_a4_l0, pE_a2_a2, pE_a2_a3,
    pE_l0_l0_l0_l0, pE_a2_l0_l0_l0, T2_20, T2_11, T2_02, T2_30, T2_21, T2_12, T2_03, T2_40, T2_31,
    T2_22, T2_13, T2_04, T2_50, T2_41, T2_32, T2_23, T2_14, T2_05, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `f_3` in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem low3_eq (s : ℝ) (y : State 2) :
    lowF3 (lin0 s y) (pv (aL2 s) y) (pv (aL3 s) y) = pv (low3L s) y := by
  have e : lowF3 (lin0 s y) (pv (aL2 s) y) (pv (aL3 s) y) = ((-1 / 6)) * (lin0 s y * lin0 s y * lin0
      s y) + ((-1 / 2)) * (pv (aL2 s) y * lin0 s y * lin0 s y) + ((-1 / 2)) * (pv (aL3 s) y * lin0 s
      y * lin0 s y) + ((-1 / 2)) * (pv (aL2 s) y * pv (aL2 s) y * lin0 s y) + ((1 / 120)) * (lin0 s
      y * lin0 s y * lin0 s y * lin0 s y * lin0 s y) := by
    simp only [lowF3]; ring
  rw [e, pE_l0_l0_l0_l0_l0_eq s y, pE_l0_l0_l0_eq s y, pE_a2_l0_l0_eq s y, pE_a3_l0_l0_eq s y,
    pE_a2_a2_l0_eq s y]
  simp only [pv, low3L, low3L4, low3L5, pE_l0_l0_l0, pE_a2_l0_l0, pE_a3_l0_l0, pE_a2_a2_l0,
    pE_l0_l0_l0_l0_l0, T3_20, T3_11, T3_02, T3_30, T3_21, T3_12, T3_03, T3_40, T3_31, T3_22, T3_13,
    T3_04, T3_50, T3_41, T3_32, T3_23, T3_14, T3_05, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  ring

/-- The Taylor polynomial of `f_1` minus its weight-five part is `O(‖y‖⁶)` (products of pieces of
total weight at least six). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem split1_isBigO (s : ℝ) :
    (fun y : State 2 => -(4 + s ^ 2) * ((1 - ux s y ^ 2 / 2 + ux s y ^ 4 / 24 - 1) * x2v s y + (ux s
    y - ux s y ^ 3 / 6 + ux s y ^ 5 / 120) * x3v s y) - lowF1 s (lin0 s y) (pv (aL2 s) y) (pv (aL3
    s) y) (pv (aL4 s) y) (lin2 s y) (pv (h1L2 s) y) (pv (h1L3 s) y) (lin3 s y) (pv (h2L2 s) y) (pv
    (h2L3 s) y) (pv (h2L4 s) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((((((((((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (o_l0 s) (o_a4 s) (by norm_num)) (o_X2 s) (by
    norm_num)).const_mul_left (4 + s ^ 2)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (o_a2 s) (o_a3 s) (by norm_num)) (o_X2 s) (by
    norm_num)).const_mul_left (4 + s ^ 2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a2 s) (o_a4 s) (by norm_num)) (o_X2 s) (by
    norm_num)).const_mul_left (4 + s ^ 2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_r3 s) (o_r3 s) (by norm_num)) (o_X2 s) (by
    norm_num)).const_mul_left (2 + (s ^ 2) / (2)))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 (o_l0 s) (o_l0 s) (by norm_num))
    (o_b4 s) (by norm_num)).const_mul_left (2 + (s ^ 2) / (2)))).add ((Dynamics.isBigO_mul_pow (k :=
    6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_l0 s) (o_a2 s) (by
    norm_num)) (o_B3 s) (by norm_num)).const_mul_left (4 + s ^ 2))).add ((Dynamics.isBigO_mul_pow (k
    := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (o_l0 s) (o_a3 s) (by
    norm_num)) (o_B s) (by norm_num)).const_mul_left (4 + s ^ 2))).add ((Dynamics.isBigO_mul_pow (k
    := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (o_a2 s) (o_a2 s) (by
    norm_num)) (o_B s) (by norm_num)).const_mul_left (2 + (s ^ 2) / (2)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r s) (o_u s) (by norm_num)) (o_u s) (by norm_num)) (o_u s) (by norm_num)) (o_X2 s) (by
    norm_num)).const_mul_left ((-1 / 6) + (-s ^ 2) / (24)))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r s) (o_u s) (by norm_num))
    (o_u s) (by norm_num)) (o_l0 s) (by norm_num)) (o_X2 s) (by norm_num)).const_mul_left ((-1 / 6)
    + (-s ^ 2) / (24)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r s) (o_u s) (by norm_num)) (o_l0 s) (by
    norm_num)) (o_l0 s) (by norm_num)) (o_X2 s) (by norm_num)).const_mul_left ((-1 / 6) + (-s ^ 2) /
    (24)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3)
    tendsto_norm0 (o_r s) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num))
    (o_X2 s) (by norm_num)).const_mul_left ((-1 / 6) + (-s ^ 2) / (24)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    (o_l0 s) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)) (o_B s) (by
    norm_num)).const_mul_left ((-1 / 6) + (-s ^ 2) / (24)))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (o_a2 s) (o_c4 s) (by norm_num)).const_mul_left (-4 - s ^ 2))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a3 s) (o_C3 s) (by norm_num)).const_mul_left
    (-4 - s ^ 2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a4 s) (o_C s) (by
    norm_num)).const_mul_left (-4 - s ^ 2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    (o_l0 s) (o_l0 s) (by norm_num)) (o_r3 s) (by norm_num)) (o_X3 s) (by norm_num)).const_mul_left
    (2 + (s ^ 2) / (2)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_l0 s) (o_r s) (by norm_num)) (o_r s) (by norm_num)) (o_X3 s) (by norm_num)).const_mul_left (2
    + (s ^ 2) / (2)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow
    (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (o_r s) (o_r s) (by
    norm_num)) (o_r s) (by norm_num)) (o_X3 s) (by norm_num)).const_mul_left ((2 / 3) + (s ^ 2) /
    (6)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 (o_l0 s) (o_l0 s) (by norm_num))
    (o_l0 s) (by norm_num)) (o_C3 s) (by norm_num)).const_mul_left ((2 / 3) + (s ^ 2) / (6)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 (o_l0 s) (o_l0 s) (by norm_num)) (o_a2 s) (by
    norm_num)) (o_C s) (by norm_num)).const_mul_left (2 + (s ^ 2) / (2)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 (o_u s) (o_u s) (by norm_num)) (o_u s) (by
    norm_num)) (o_u s) (by norm_num)) (o_u s) (by norm_num)) (o_X3 s) (by norm_num)).const_mul_left
    ((-1 / 30) + (-s ^ 2) / (120)))).congr_left fun y => ?_
  simp only [ux, x2v, x3v, lowF1]
  ring

/-- The Taylor polynomial of `f_2` minus its weight-five part is `O(‖y‖⁶)` (products of pieces of
total weight at least six). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem split2_isBigO (s : ℝ) :
    (fun y : State 2 => 1 - ux s y ^ 2 / 2 + ux s y ^ 4 / 24 - 1 - lowF2 (lin0 s y) (pv (aL2 s) y)
    (pv (aL3 s) y) (pv (aL4 s) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a2 s) (o_a4 s) (by
    norm_num)).const_mul_left (-1)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_r3 s)
    (o_r3 s) (by norm_num)).const_mul_left ((-1 / 2)))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 (o_l0 s) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)) (o_r3 s) (by
    norm_num)).const_mul_left ((1 / 6)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    (o_l0 s) (o_l0 s) (by norm_num)) (o_r s) (by norm_num)) (o_r s) (by norm_num)).const_mul_left
    ((1 / 4)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k :=
    5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_l0 s) (o_r s) (by norm_num))
    (o_r s) (by norm_num)) (o_r s) (by norm_num)).const_mul_left ((1 / 6)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (o_r s) (o_r s) (by norm_num)) (o_r s) (by
    norm_num)) (o_r s) (by norm_num)).const_mul_left ((1 / 24)))).congr_left fun y => ?_
  simp only [ux, lowF2]
  ring

/-- The Taylor polynomial of `f_3` minus its weight-five part is `O(‖y‖⁶)` (products of pieces of
total weight at least six). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem split3_isBigO (s : ℝ) :
    (fun y : State 2 => ux s y - ux s y ^ 3 / 6 + ux s y ^ 5 / 120 - ux s y - lowF3 (lin0 s y) (pv
    (aL2 s) y) (pv (aL3 s) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 (o_l0 s) (o_l0 s) (by norm_num)) (o_a4 s) (by norm_num)).const_mul_left ((-1 /
    2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3)
    tendsto_norm0 (o_l0 s) (o_a2 s) (by norm_num)) (o_a3 s) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_l0 s) (o_a2 s) (by norm_num)) (o_a4 s) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (o_l0 s) (o_r3 s) (by norm_num)) (o_r3 s) (by norm_num)).const_mul_left ((-1 / 2)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (o_r s) (o_r s) (by norm_num)) (o_r s) (by norm_num)).const_mul_left ((-1 / 6)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r s) (o_u s) (by norm_num)) (o_u s) (by norm_num)) (o_u s) (by norm_num)) (o_u s) (by
    norm_num)).const_mul_left ((1 / 120)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r s) (o_u s) (by norm_num)) (o_u s) (by
    norm_num)) (o_u s) (by norm_num)) (o_l0 s) (by norm_num)).const_mul_left ((1 / 120)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r s) (o_u s) (by norm_num)) (o_u s) (by norm_num)) (o_l0 s) (by norm_num)) (o_l0 s) (by
    norm_num)).const_mul_left ((1 / 120)))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r s) (o_u s) (by norm_num)) (o_l0 s) (by
    norm_num)) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)).const_mul_left ((1 / 120)))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r s) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)) (o_l0 s) (by norm_num)) (o_l0 s) (by
    norm_num)).const_mul_left ((1 / 120)))).congr_left fun y => ?_
  simp only [ux, lowF3]
  ring

@[tmio M, powerlib_domain] private theorem ux_isBigO (s : ℝ) :
    (fun y => ux s y) =O[𝓝 0] fun y => ‖y‖ :=
  (o_u s).congr_right fun _ => pow_one _

@[tmio M, powerlib_domain] private theorem ux_tendsto (s : ℝ) :
    Tendsto (fun y => ux s y) (𝓝 0) (𝓝 0) :=
  (ux_isBigO s).trans_tendsto tendsto_norm0

/-- **`f₁` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`** (sixth-order Taylor
remainders of `cos`, `sin` and products of pieces of weight at least six). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem f1_sub_low (s : ℝ) :
    (fun y => f1v s y - pv (low1L s) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hc := Dynamics.isBigO_comp_pow Dynamics.cos_sub_taylor_isBigO (ux_tendsto s) (ux_isBigO s)
  have hn := Dynamics.isBigO_comp_pow Dynamics.sin_sub_taylor5_isBigO (ux_tendsto s) (ux_isBigO s)
  have h1 := Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 hc (o_X2 s) (by norm_num)
  have h2 := Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 hn (o_X3 s) (by norm_num)
  refine (((h1.add h2).const_mul_left (-(4 + s ^ 2))).add (split1_isBigO s)).congr_left
    fun y => ?_
  simp only [← low1_eq s y, f1v]
  ring

/-- **`f₂ = cos x₀ − 1` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem f2_sub_low (s : ℝ) :
    (fun y => Real.cos (ux s y) - 1 - pv (low2L s) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hc := Dynamics.isBigO_comp_pow Dynamics.cos_sub_taylor_isBigO (ux_tendsto s) (ux_isBigO s)
  refine (hc.add (split2_isBigO s)).congr_left fun y => ?_
  simp only [← low2_eq s y]
  ring

/-- **`f₃ = sin x₀ − x₀` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem f3_sub_low (s : ℝ) :
    (fun y => Real.sin (ux s y) - ux s y - pv (low3L s) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hn := Dynamics.isBigO_comp_pow Dynamics.sin_sub_taylor5_isBigO (ux_tendsto s) (ux_isBigO s)
  refine (hn.add (split3_isBigO s)).congr_left fun y => ?_
  simp only [← low3_eq s y]
  ring

/-! ## The quintic jet of the chart field -/

/-- The jet in the chart coordinates of the truncated nonlinearities. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem jetF_eq {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    poly3 (jet s).F a b 0 = PV0_1 s * poly3 (low1L s) a b 0 + PV0_2 s * poly3 (low2L s) a b 0 +
    PV0_3 s * poly3 (low3L s) a b 0 := by
  simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4,
    PlanarFocus.Jet5.F5, jet, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L, low3L4, low3L5,
    poly3_cons, poly3_nil, List.cons_append, List.nil_append, JA_20_eq hs, JA_11_eq hs, JA_02_eq hs,
    JA_30_eq hs, JA_21_eq hs, JA_12_eq hs, JA_03_eq hs, JA_40_eq hs, JA_31_eq hs, JA_22_eq hs,
    JA_13_eq hs, JA_04_eq hs, JA_50_eq hs, JA_41_eq hs, JA_32_eq hs, JA_23_eq hs, JA_14_eq hs,
    JA_05_eq hs]
  ring

/-- The jet in the chart coordinates of the truncated nonlinearities. Static evidence on the model.
-/
@[tmio M, powerlib_domain] theorem jetG_eq {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    poly3 (jet s).G a b 0 = PV1_1 s * poly3 (low1L s) a b 0 + PV1_2 s * poly3 (low2L s) a b 0 +
    PV1_3 s * poly3 (low3L s) a b 0 := by
  simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet.G2, PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4,
    PlanarFocus.Jet5.G5, jet, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L, low3L4, low3L5,
    poly3_cons, poly3_nil, List.cons_append, List.nil_append, JB_20_eq hs, JB_11_eq hs, JB_02_eq hs,
    JB_30_eq hs, JB_21_eq hs, JB_12_eq hs, JB_03_eq hs, JB_40_eq hs, JB_31_eq hs, JB_22_eq hs,
    JB_13_eq hs, JB_04_eq hs, JB_50_eq hs, JB_41_eq hs, JB_32_eq hs, JB_23_eq hs, JB_14_eq hs,
    JB_05_eq hs]
  ring

/-- **The first chart coordinate has the jet `J`**: `G₀ − F_J = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G0_sub_jet {s : ℝ} (hs : 0 < s) :
    (fun y => G0 s y - poly3 (jet s).F (y 0) (y 1) 0) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine ((((f1_sub_low s).const_mul_left (PV0_1 s)).add
    ((f2_sub_low s).const_mul_left (PV0_2 s))).add
      ((f3_sub_low s).const_mul_left (PV0_3 s))).congr_left fun y => ?_
  rw [(G_eq hs y).1, jetF_eq hs]
  simp only [pv]; ring

/-- **The second chart coordinate has the jet `J`**: `G₁ − G_J = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G1_sub_jet {s : ℝ} (hs : 0 < s) :
    (fun y => G1 s y - poly3 (jet s).G (y 0) (y 1) 0) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine ((((f1_sub_low s).const_mul_left (PV1_1 s)).add
    ((f2_sub_low s).const_mul_left (PV1_2 s))).add
      ((f3_sub_low s).const_mul_left (PV1_3 s))).congr_left fun y => ?_
  rw [(G_eq hs y).2, jetG_eq hs]
  simp only [pv]; ring

/-- The tails of the jet: `G − J₃ = O(‖y‖⁴)` and `G − J₄ = O(‖y‖⁵)` in both coordinates. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_tail_bounds {s : ℝ} (hs : 0 < s) :
    ((fun y => G0 s y - poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) =O[𝓝 0]
        fun y => ‖y‖ ^ 4) ∧
      ((fun y => G1 s y - poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0) =O[𝓝 0]
        fun y => ‖y‖ ^ 4) ∧
      ((fun y => G0 s y - poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y 1) 0) =O[𝓝 0]
        fun y => ‖y‖ ^ 5) ∧
      ((fun y => G1 s y - poly3 ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0) =O[𝓝 0]
        fun y => ‖y‖ ^ 5) := by
  have hF4 : (fun y : State 2 => pv (jet s).F4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
    pv_isBigO _ (by simp [PlanarFocus.Jet5.F4])
  have hF5 : (fun y : State 2 => pv (jet s).F5 y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [PlanarFocus.Jet5.F5])
  have hG4 : (fun y : State 2 => pv (jet s).G4 y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
    pv_isBigO _ (by simp [PlanarFocus.Jet5.G4])
  have hG5 : (fun y : State 2 => pv (jet s).G5 y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [PlanarFocus.Jet5.G5])
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((mono (G0_sub_jet hs) (by norm_num)).add (hF4.add (mono hF5 (by norm_num)))).congr_left
      fun y => ?_
    simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono (G1_sub_jet hs) (by norm_num)).add (hG4.add (mono hG5 (by norm_num)))).congr_left
      fun y => ?_
    simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono (G0_sub_jet hs) (by norm_num)).add hF5).congr_left fun y => ?_
    simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono (G1_sub_jet hs) (by norm_num)).add hG5).congr_left fun y => ?_
    simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet5.poly3_append, pv]; ring

/-! ## The invariance defect -/

/-- The `w₁`-component of the invariance defect over `y`. -/
def dcomp2 (s : ℝ) (y : State 2) : ℝ :=
  dpoly3 (h1L s) (y 0) (y 1) 0 (-(y 1) + G0 s y) (y 0 + G1 s y) 0 + s * pv (h1L s) y -
    pv (h2L s) y - (Real.cos (ux s y) - 1) + ((s - 2) * G0 s y + (s + 2) * G1 s y)

/-- The `w₂`-component of the invariance defect over `y`. -/
def dcomp3 (s : ℝ) (y : State 2) : ℝ :=
  dpoly3 (h2L s) (y 0) (y 1) 0 (-(y 1) + G0 s y) (y 0 + G1 s y) 0 + 2 * pv (h1L s) y +
    (2 / s + s) * pv (h2L s) y - (Real.sin (ux s y) - ux s y) +
      ((s ^ 2 + 2 - s) * G0 s y + (s ^ 2 + 2 + s) * G1 s y)

/-- The polynomial part of the defect, component `2`: the homological coefficients and the terms of
degree five and six. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main2_eq (s : ℝ) (y : State 2) :
    dpoly3 (h1L s) (y 0) (y 1) 0 (-(y 1) + poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) (y 0 +
    poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0) 0 + s * pv (h1L s) y - pv (h2L s) y - pv (low2L4
    s) y + ((s - 2) * poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y 1) 0 + (s + 2) * poly3
    ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0) = pv (highD2 s) y + (Hom2_02 s * (y 0 ^
    0 * y 1 ^ 2) + Hom2_03 s * (y 0 ^ 0 * y 1 ^ 3) + Hom2_04 s * (y 0 ^ 0 * y 1 ^ 4) + Hom2_11 s *
    (y 0 ^ 1 * y 1 ^ 1) + Hom2_12 s * (y 0 ^ 1 * y 1 ^ 2) + Hom2_13 s * (y 0 ^ 1 * y 1 ^ 3) +
    Hom2_20 s * (y 0 ^ 2 * y 1 ^ 0) + Hom2_21 s * (y 0 ^ 2 * y 1 ^ 1) + Hom2_22 s * (y 0 ^ 2 * y 1 ^
    2) + Hom2_30 s * (y 0 ^ 3 * y 1 ^ 0) + Hom2_31 s * (y 0 ^ 3 * y 1 ^ 1) + Hom2_40 s * (y 0 ^ 4 *
    y 1 ^ 0)) := by
  simp only [dpoly3_cons, dpoly3_nil, poly3_cons, poly3_nil, h1L, h2L, h1L2, h1L3, h1L4, h2L2, h2L3,
    h2L4, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4, PlanarFocus.Jet.G2,
    PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4, jet, low2L4, highD2, pv, List.cons_append,
    List.nil_append, Hom2_02, Hom2_03, Hom2_04, Hom2_11, Hom2_12, Hom2_13, Hom2_20, Hom2_21,
    Hom2_22, Hom2_30, Hom2_31, Hom2_40]
  ring

/-- **The homological equations make the polynomial part of the defect of degree at least five**,
component `2`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main2_eq_high {s : ℝ} (hs : 0 < s) (y : State 2) :
    dpoly3 (h1L s) (y 0) (y 1) 0 (-(y 1) + poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) (y 0 +
    poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0) 0 + s * pv (h1L s) y - pv (h2L s) y - pv (low2L4
    s) y + ((s - 2) * poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y 1) 0 + (s + 2) * poly3
    ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0) = pv (highD2 s) y := by
  rw [main2_eq, Hom2_02_eq hs, Hom2_03_eq hs, Hom2_04_eq hs, Hom2_11_eq hs, Hom2_12_eq hs,
    Hom2_13_eq hs, Hom2_20_eq hs, Hom2_21_eq hs, Hom2_22_eq hs, Hom2_30_eq hs, Hom2_31_eq hs,
    Hom2_40_eq hs]
  ring

/-- The polynomial part of the defect, component `3`: the homological coefficients and the terms of
degree five and six. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main3_eq (s : ℝ) (y : State 2) :
    dpoly3 (h2L s) (y 0) (y 1) 0 (-(y 1) + poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) (y 0 +
    poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0) 0 + 2 * pv (h1L s) y + (2 / s + s) * pv (h2L s)
    y - pv (low3L4 s) y + ((s ^ 2 + 2 - s) * poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y
    1) 0 + (s ^ 2 + 2 + s) * poly3 ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0) = pv
    (highD3 s) y + (Hom3_02 s * (y 0 ^ 0 * y 1 ^ 2) + Hom3_03 s * (y 0 ^ 0 * y 1 ^ 3) + Hom3_04 s *
    (y 0 ^ 0 * y 1 ^ 4) + Hom3_11 s * (y 0 ^ 1 * y 1 ^ 1) + Hom3_12 s * (y 0 ^ 1 * y 1 ^ 2) +
    Hom3_13 s * (y 0 ^ 1 * y 1 ^ 3) + Hom3_20 s * (y 0 ^ 2 * y 1 ^ 0) + Hom3_21 s * (y 0 ^ 2 * y 1 ^
    1) + Hom3_22 s * (y 0 ^ 2 * y 1 ^ 2) + Hom3_30 s * (y 0 ^ 3 * y 1 ^ 0) + Hom3_31 s * (y 0 ^ 3 *
    y 1 ^ 1) + Hom3_40 s * (y 0 ^ 4 * y 1 ^ 0)) := by
  simp only [dpoly3_cons, dpoly3_nil, poly3_cons, poly3_nil, h1L, h2L, h1L2, h1L3, h1L4, h2L2, h2L3,
    h2L4, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4, PlanarFocus.Jet.G2,
    PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4, jet, low3L4, highD3, pv, List.cons_append,
    List.nil_append, Hom3_02, Hom3_03, Hom3_04, Hom3_11, Hom3_12, Hom3_13, Hom3_20, Hom3_21,
    Hom3_22, Hom3_30, Hom3_31, Hom3_40]
  ring

/-- **The homological equations make the polynomial part of the defect of degree at least five**,
component `3`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main3_eq_high {s : ℝ} (hs : 0 < s) (y : State 2) :
    dpoly3 (h2L s) (y 0) (y 1) 0 (-(y 1) + poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) (y 0 +
    poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0) 0 + 2 * pv (h1L s) y + (2 / s + s) * pv (h2L s)
    y - pv (low3L4 s) y + ((s ^ 2 + 2 - s) * poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y
    1) 0 + (s ^ 2 + 2 + s) * poly3 ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0) = pv
    (highD3 s) y := by
  rw [main3_eq, Hom3_02_eq hs, Hom3_03_eq hs, Hom3_04_eq hs, Hom3_11_eq hs, Hom3_12_eq hs,
    Hom3_13_eq hs, Hom3_20_eq hs, Hom3_21_eq hs, Hom3_22_eq hs, Hom3_30_eq hs, Hom3_31_eq hs,
    Hom3_40_eq hs]
  ring

/-- **The invariance defect at a chart point** is `d₂(y) w₁ + d₃(y) w₂`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem defect_eq {s : ℝ} (hs : 0 < s) (y : State 2) :
    invarianceDefect (fderiv ℝ (bautinPath s).field 0) (critP (bautinPathQ s) (bautinPathP s))
      (fnl s) (manifold s) (critι (bautinPathQ s) y) = dcomp2 s y • w1 s + dcomp3 s y • w2 s := by
  have hc := isCritical_bautin hs
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_manifoldH s y
  have hdef := invarianceDefect_comp_chart (A := fderiv ℝ (bautinPath s).field 0) (f := fnl s)
    hc.isChart hL.differentiableAt
  rw [show (fun x => manifoldH s (critπ (bautinPathP s) x)) = manifold s from rfl, hL.fderiv]
    at hdef
  rw [hdef]
  have hφ : manifold s (critι (bautinPathQ s) y) = manifoldH s y := by
    rw [manifold, hc.critπ_critι]
  have hN : normalField (fderiv ℝ (bautinPath s).field 0) (critP (bautinPathQ s) (bautinPathP s))
      (fnl s) (manifold s) (critι (bautinPathQ s) y) =
        fderiv ℝ (bautinPath s).field 0 (manifoldH s y) + (fnl s (chartPt s y) -
          critι (bautinPathQ s) (critπ (bautinPathP s) (fnl s (chartPt s y)))) := by
    rw [normalField, hφ]
    have h1 : critπ (bautinPathP s) (fderiv ℝ (bautinPath s).field 0 (manifoldH s y)) = 0 := by
      rw [hc.critπ_apply, critπ_manifoldH hs, map_zero]
    simp [critP, h1, chartPt]
  have hker : critπ (bautinPathP s) (L (chartField (fderiv ℝ (bautinPath s).field 0) (fnl s)
      (manifold s) (critι (bautinPathQ s)) (critπ (bautinPathP s)) y) -
      normalField (fderiv ℝ (bautinPath s).field 0) (critP (bautinPathQ s) (bautinPathP s))
        (fnl s) (manifold s) (critι (bautinPathQ s) y)) = 0 := by
    rw [hLv, hN]
    simp only [map_sub, map_add, map_smul, critπ_w1 hs, critπ_w2 hs, hc.critπ_apply,
      critπ_manifoldH hs, hc.critπ_critι]
    simp
  rw [ker_decomp hs hker, hLv, hN, chartField_eq hs]
  obtain ⟨c0, c2, c3⟩ := chartPt_apply hs y
  congr 2
  · simp [w1, w2, A_apply hs, fnl_apply hs, critι_bautin, rotL_apply0, rotL_apply1, manifoldH, c0,
      dcomp2, pv, G0, G1]
    ring
  · simp [w1, w2, A_apply hs, fnl_apply hs, critι_bautin, rotL_apply0, rotL_apply1, manifoldH, c0,
      dcomp3, pv, G0, G1]
    ring

/-- The `w₁`-component of the defect is `O(‖y‖⁵)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dcomp2_isBigO {s : ℝ} (hs : 0 < s) :
    (fun y => dcomp2 s y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := by
  have e : ∀ y, dcomp2 s y = pv (highD2 s) y +
      (poly3 ((h1L s).map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0 *
          (G0 s y - poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) +
        poly3 ((h1L s).map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0 *
          (G1 s y - poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0)) -
      (Real.cos (ux s y) - 1 - pv (low2L4 s) y) +
      ((s - 2) * (G0 s y - poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y 1) 0) +
        (s + 2) * (G1 s y - poly3 ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0)) := by
    intro y
    rw [← main2_eq_high hs y, dcomp2, Dynamics.Degenerate.dpoly3_eq_partials,
      Dynamics.Degenerate.dpoly3_eq_partials]
    ring
  have hs' := jet_tail_bounds hs
  obtain ⟨hG0_3, hG1_3, hG0_4, hG1_4⟩ := hs'
  have hdx : (fun y : State 2 => poly3 ((h1L s).map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [h1L, h1L2, h1L3, h1L4, Dynamics.Degenerate.dxTerm])
  have hdy : (fun y : State 2 => poly3 ((h1L s).map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [h1L, h1L2, h1L3, h1L4, Dynamics.Degenerate.dyTerm])
  have hcos : (fun y : State 2 => Real.cos (ux s y) - 1 - pv (low2L4 s) y) =O[𝓝 0]
      fun y => ‖y‖ ^ 5 :=
    ((mono (f2_sub_low s) (by norm_num)).add (pv_isBigO (low2L5 s) (by simp [low2L5]))).congr_left
      fun y => by simp only [low2L, pv, PlanarFocus.Jet5.poly3_append]; ring
  have hhigh : (fun y : State 2 => pv (highD2 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [highD2])
  refine (((hhigh.add ((Dynamics.isBigO_mul_pow tendsto_norm0 hdx hG0_3 (by norm_num)).add
    (Dynamics.isBigO_mul_pow tendsto_norm0 hdy hG1_3 (by norm_num)))).sub hcos).add
      ((hG0_4.const_mul_left (s - 2)).add (hG1_4.const_mul_left (s + 2)))).congr_left fun y => ?_
  rw [e y]

/-- The `w₂`-component of the defect is `O(‖y‖⁵)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dcomp3_isBigO {s : ℝ} (hs : 0 < s) :
    (fun y => dcomp3 s y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := by
  have e : ∀ y, dcomp3 s y = pv (highD3 s) y +
      (poly3 ((h2L s).map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0 *
          (G0 s y - poly3 ((jet s).F2 ++ (jet s).F3) (y 0) (y 1) 0) +
        poly3 ((h2L s).map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0 *
          (G1 s y - poly3 ((jet s).G2 ++ (jet s).G3) (y 0) (y 1) 0)) -
      (Real.sin (ux s y) - ux s y - pv (low3L4 s) y) +
      ((s ^ 2 + 2 - s) * (G0 s y - poly3 ((jet s).F2 ++ (jet s).F3 ++ (jet s).F4) (y 0) (y 1) 0) +
        (s ^ 2 + 2 + s) *
          (G1 s y - poly3 ((jet s).G2 ++ (jet s).G3 ++ (jet s).G4) (y 0) (y 1) 0)) := by
    intro y
    rw [← main3_eq_high hs y, dcomp3, Dynamics.Degenerate.dpoly3_eq_partials,
      Dynamics.Degenerate.dpoly3_eq_partials]
    ring
  obtain ⟨hG0_3, hG1_3, hG0_4, hG1_4⟩ := jet_tail_bounds hs
  have hdx : (fun y : State 2 => poly3 ((h2L s).map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [h2L, h2L2, h2L3, h2L4, Dynamics.Degenerate.dxTerm])
  have hdy : (fun y : State 2 => poly3 ((h2L s).map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [h2L, h2L2, h2L3, h2L4, Dynamics.Degenerate.dyTerm])
  have hsin : (fun y : State 2 => Real.sin (ux s y) - ux s y - pv (low3L4 s) y) =O[𝓝 0]
      fun y => ‖y‖ ^ 5 :=
    ((mono (f3_sub_low s) (by norm_num)).add (pv_isBigO (low3L5 s) (by simp [low3L5]))).congr_left
      fun y => by simp only [low3L, pv, PlanarFocus.Jet5.poly3_append]; ring
  have hhigh : (fun y : State 2 => pv (highD3 s) y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [highD3])
  refine (((hhigh.add ((Dynamics.isBigO_mul_pow tendsto_norm0 hdx hG0_3 (by norm_num)).add
    (Dynamics.isBigO_mul_pow tendsto_norm0 hdy hG1_3 (by norm_num)))).sub hsin).add
      ((hG0_4.const_mul_left (s ^ 2 + 2 - s)).add
        (hG1_4.const_mul_left (s ^ 2 + 2 + s)))).congr_left fun y => ?_
  rw [e y]

/-- **The invariance defect is `O(‖u‖⁵)` on the centre subspace.** Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem isOrder_defect {s : ℝ} (hs : 0 < s) :
    IsOrder (critP (bautinPathQ s) (bautinPathP s))
      (invarianceDefect (fderiv ℝ (bautinPath s).field 0) (critP (bautinPathQ s) (bautinPathP s))
        (fnl s) (manifold s)) 5 := by
  have h := (isCritical_bautin hs).isChart.isOrder_of_isBigO (k := 5)
    (G := invarianceDefect (fderiv ℝ (bautinPath s).field 0)
      (critP (bautinPathQ s) (bautinPathP s)) (fnl s) (manifold s)) ?_
  · exact_mod_cast h
  have h2 : (fun y : State 2 => dcomp2 s y • w1 s) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (IsBigO.of_bound ‖w1 s‖ (Eventually.of_forall fun y => by
      rw [norm_smul, mul_comm])).trans (dcomp2_isBigO hs)
  have h3 : (fun y : State 2 => dcomp3 s y • w2 s) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (IsBigO.of_bound ‖w2 s‖ (Eventually.of_forall fun y => by
      rw [norm_smul, mul_comm])).trans (dcomp3_isBigO hs)
  exact (h2.add h3).congr_left fun y => (defect_eq hs y).symm

/-! ## The second Lyapunov coefficient at the degenerate point -/

/-- `l₁(J) = 0` at a zero of `bautinNum`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1_eq_zero {s : ℝ} (hs : 0 < s) (hN : bautinNum s = 0) :
    (jet s).l1 1 = 0 := by
  rw [jet_l1_eq hs, hN]; simp

/-- **`l₂(J) > 0` at the degenerate point.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l2_pos {s : ℝ} (hN : bautinNum s = 0) (h2 : 2 < s)
    (h21 : s < 21 / 10) : 0 < (jet s).l2 1 := by
  rw [jet_l2 (by linarith)]; exact L2V_pos hN h2 h21

end Bautin

open Bautin in
/-- **The degenerate Hopf point of the path is unstable**: at the zero `s > 0` of `bautinNum`
(`ℓ₁ = 0`) the boundary point is a weak focus of the second order with `l₂ > 0` in the critical
chart (the approximate centre manifold `Bautin.manifold s`, invariance defect `O(‖u‖⁵)`, the
quintic jet `Bautin.jet s`; `mem_den_unstable_of_secondLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem bautinPath_mem_den_unstable_of_bautinNum_eq_zero {s : ℝ}
    (hs : 0 < s) (hN : bautinNum s = 0) :
    connection% (bautinPath s ∈ family.den (.flow .unstable)) := by
  have h2 : 2 < s := by
    by_contra h
    linarith [bautinNum_neg hs (not_lt.mp h)]
  have h21 : s < 21 / 10 := by
    by_contra h
    linarith [bautinNum_pos (not_lt.mp h)]
  obtain ⟨h3, h1, h0, hH⟩ := bautinPath_boundary hs
  refine mem_den_unstable_of_secondLyapunov_pos (bautinPath s) h3 h1 h0 hH
    (bautinPath_isCriticalPair hs) (contDiffAt_manifold s) (manifold_zero s)
    (fderiv_manifold_zero s) (critP_manifold hs) (isOrder_defect hs) (J := jet s) ?_ ?_
    (jet_l1_eq_zero hs hN) (jet_l2_pos hN h2 h21)
  · refine ((G0_sub_jet hs).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => (bautinPath s).field x - fderiv ℝ (bautinPath s).field 0 x) = fnl s
      from rfl, chartField_eq hs, G0]
    simp only [Dynamics.Degenerate.PlanarFocus.frameX_apply,
      Dynamics.Degenerate.PlanarFocus.frameY_apply, PiLp.add_apply, rotL_apply0]
    ring_nf
  · refine ((G1_sub_jet hs).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => (bautinPath s).field x - fderiv ℝ (bautinPath s).field 0 x) = fnl s
      from rfl, chartField_eq hs, G1]
    simp only [Dynamics.Degenerate.PlanarFocus.frameX_apply,
      Dynamics.Degenerate.PlanarFocus.frameY_apply, PiLp.add_apply, rotL_apply0, rotL_apply1]
    ring_nf

end VSM
end powerlib.GFM.Line
