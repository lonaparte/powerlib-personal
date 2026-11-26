import theorem.GridTiedConverter.GFM.HopfLinePSC
import theorem.Dynamics.CenterReductionBautin
import theorem.Dynamics.CenterManifoldChart

/-! # The Bautin point of power synchronization on a dynamic R–L line is unstable

Domain module.

Model boundary.
* The three-state power-synchronization law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged (state `(δ, i_d, i_q)`, grid dq
  frame, export-positive power, `δ̇ = K_p (P_ref − P_e)`, `L i̇ = E e^{jδ} − V − (R + jX) i`), read
  about a selected angle (`Line.PSC.Model`) on `Line.PSC.family`. Excluded as there.
* The family laws: a model on the Hopf boundary of the monic cubic (`a₁, a₀ > 0`, `a₂ a₁ = a₀`) with
  a critical pair `(q, p)` at `ω`, read in ANY chart `ι`, `π` of the critical plane
  (`IsChart (critP q p) ι π`) with a planar linear part `L₂`, `L₂² = −ω²`, and the rotation
  coordinates `frameX`, `frameY L₂ ω` of `L₂`; the critical chart (`critι q`, `critπ p`,
  `rotL ω`) is one instance.
* The degenerate point: the unit line `Line.PSC.unitLine (6/5) 20` (`E = R = L = ω₀ = 1`,
  `V = 6/5`, `K_p = 20`, `P_ref = −1/10`, `δ* = 0`, operating current `(−1/10, 1/10)`), where
  `det(sI − J) = (s² + 6)(s + 4)` and `ℓ₁ = 0` (`Line.PSC.unitLine_bautin_firstLyapunov`). The
  translated field is `F = A x + f(x)` with `A = [[−2, −20, 0], [0, −1, 1], [1, −1, −1]]` and
  `f = (2(cos x₀ − 1) − 20((cos x₀ − 1) x₁ + sin x₀ · x₂) − 2(sin x₀ − x₀), cos x₀ − 1,
  sin x₀ − x₀)` (`Line.PSC.Bautin.fnl_apply`).
* The chart: the rational chart `ι' y = y₀ a + y₁ b`, `a = Re q = (−4, 1, 1)`,
  `b = Im q/√6 = (2, 0, 1)`, of the explicit critical pair `Bautin.qv`, `Bautin.pv3` at `ω = √6`,
  and its left inverse `π'` vanishing on the stable eigenvector `w = (10, 1, −3)` (`A w = −4 w`);
  the reduced linear part is `rotR y = (y₁, −6 y₀)` and the rotation coordinates are
  `(y₀, −y₁/√6)`. The approximate centre manifold is `Bautin.manifold = H ∘ π'`, `H(y) = h(y) w`,
  `h` a polynomial of degrees two to four with rational coefficients.
* Level: exact. The trigonometric nonlinearities enter through the sixth-order Taylor remainders
  of `cos` and `sin`; the homological identities of degrees two to four and every polynomial
  identity of the chart are rational (`ring`); `l₁ = 0` and `l₂ = 51200√6/77` are computed in
  `ℚ(√6)` (`linear_combination` with `(√6)² = 6`). No floating point, sampling or search.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3 (Bautin points, the
second Lyapunov coefficient); Carr, *Applications of Centre Manifold Theory* (1981), §2.4–2.5
(reduction principle, approximation of the centre manifold). The generic laws are
`theorem/Dynamics/CenterReductionBautin.lean` (`unstable_of_dichotomy_reduced_l2_pos`,
`localAsymptoticStable_of_dichotomy_reduced_l2_neg`), the dichotomy
`theorem/Dynamics/HopfDichotomy.lean` (`IsCritical.exists_dichotomy`),
`theorem/Dynamics/CenterManifoldChart.lean` (defect in a chart, Taylor remainders) and
`theorem/Dynamics/Degenerate/PlanarFocus2.lean` (`Jet5.l1_nrm`, `Jet5.l2_nrm`); the method is
that of the four-state template `theorem/GridTiedConverter/GFM/HopfBautinPoint.lean`. The centre
manifold, the jet and the Lyapunov chain were derived with SymPy in exact rational and `ℚ(√6)`
arithmetic (untrusted, discovery evidence only); every identity is checked here.

Results.
* The model at the point: `Line.PSC.Bautin.bpt` (`= unitLine (6/5) 20`), `Bautin.bpt_Q`,
  `Bautin.bpt_coeffs` (`a₂ = 4`, `a₁ = 6`, `a₀ = 24`), `Bautin.bpt_point`,
  `Bautin.fderiv_field_zero`, `Bautin.A_apply`, `Bautin.fnl`, `Bautin.fnl_apply`,
  `Bautin.bpt_field_zero`; `Bautin.r` (`= √6`), `Bautin.r_pos`, `Bautin.r_sq`.
* The critical pair and the chart: `Bautin.qv`, `Bautin.pv3`, `Bautin.isCriticalPair_bpt`;
  `Bautin.iotaR`, `Bautin.piR`, `Bautin.rotR`, `Bautin.wv`, `Bautin.iotaR_apply`,
  `Bautin.piR_apply`, `Bautin.rotR_apply`, `Bautin.rotR_rotR`, `Bautin.piR_iotaR`,
  `Bautin.piR_wv`, `Bautin.A_wv`, `Bautin.piR_A_iotaR`, **`Bautin.isChart_R`** (`ι'π' = critP q p`),
  `Bautin.sub_iotaR_piR` (`(1 − P) v = (v₁ − (π' v)₀) w`).
* The manifold: `Bautin.hL2` … `Bautin.hL4`, `Bautin.hL`, `Bautin.manifoldH`, `Bautin.manifold`,
  `Bautin.piR_manifoldH`, `Bautin.hasFDerivAt_manifoldH`, `Bautin.contDiffAt_manifold`,
  `Bautin.manifold_zero`, `Bautin.fderiv_manifold_zero`, `Bautin.critP_manifold`.
* The chart field and its quintic jet: `Bautin.chartPt`, `Bautin.chartField_eq`,
  `Bautin.chartPt_apply`, `Bautin.G0`, `Bautin.G1`, `Bautin.f0v`, `Bautin.G_eq`; the truncations
  `Bautin.low1_eq` … `Bautin.low3_eq`, `Bautin.split1_isBigO` … `Bautin.split3_isBigO`,
  `Bautin.f1_sub_low` … `Bautin.f3_sub_low`; `Bautin.cF`, `Bautin.cG`, `Bautin.cF_eq`,
  `Bautin.cG_eq`, `Bautin.G0_sub_jet`, `Bautin.G1_sub_jet`, `Bautin.jet_tail_bounds`.
* **The invariance defect is `O(‖u‖⁵)`**: `Bautin.dcomp`, `Bautin.main_eq_high` (the homological
  equations of degrees two to four), `Bautin.defect_eq`, `Bautin.dcomp_isBigO`,
  `Bautin.isOrder_defect`.
* The jet in the rotation frame: `Bautin.jet`, `Bautin.jetN` (`= jet/√6`, `Bautin.jet_nrm`),
  `Bautin.frameY_rotR`, `Bautin.jetF_frame`, `Bautin.jetG_frame`; the Lyapunov chain
  `Bautin.jv_c30` … `Bautin.jv_l2`; **`Bautin.jet_l1_eq_zero`** (`l₁(J) = 0`) and
  **`Bautin.jet_l2_eq`** (`l₂(J) = 51200√6/77 > 0`).

Family and connection conclusions.
No new family: connection conclusions on `Line.PSC.family`.
* `Line.PSC.mem_den_unstable_of_secondLyapunov_pos`,
  `Line.PSC.mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`: a degenerate Hopf point
  of the cubic (`l₁(J) = 0`) with `l₂(J) > 0` is unstable, with `l₂(J) < 0` locally
  asymptotically stable, for an approximate centre manifold with invariance defect `O(‖u‖⁵)`
  and the quintic jet `J` of its chart field in any chart of the critical plane.
* **`Line.PSC.unitLine_bautin_mem_den_unstable`**: the degenerate point `V = 6/5`, `K_p = 20` of
  the unit line is unstable (a weak focus of the second order, `l₂ > 0`; Bautin point with a
  subcritical second-order focus). The other degenerate points of `Line.PSC.Model.Degenerate`
  (the zeros of `𝔅_P` elsewhere on the Hopf boundary, the Bogdanov–Takens and zero–Hopf fold
  points) are not decided here.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace PSC

open Complex Matrix Polynomial Filter Topology Asymptotics
open powerlib.Dynamics (State)
open powerlib.Dynamics.LyapunovPerron (expFlow)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold
open powerlib.Dynamics.Degenerate
open powerlib.Dynamics.Degenerate.PlanarFocus (frameX frameY Jet5)

section Degenerate

@[tmio M, powerlib_domain] private theorem bautin_coeff2_pos {m : Model}
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) : 0 < m.g.coeff2 m.Q := by
  by_contra h
  push Not at h
  nlinarith

/-- The reduction data at a boundary point with a critical pair: the dichotomy of `critP q p`
(`ε = 0`), the commuting projection and the nonlinear part `F − DF(0)`. -/
@[tmio M, powerlib_domain] private theorem bautin_reductionData (m : Model)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    ∃ K β : ℝ, 0 < β ∧
      (∀ t, ‖expFlow (fderiv ℝ m.field 0) t * critP q p‖ ≤ K * Real.exp (0 * |t|)) ∧
      (∀ t, 0 ≤ t → ‖expFlow (fderiv ℝ m.field 0) t * (1 - critP q p)‖ ≤
        K * Real.exp (-(β * t))) ∧
      IsCommutingProjection (fderiv ℝ m.field 0) (critP q p) ∧
      fullField (fderiv ℝ m.field 0) (fun x => m.field x - fderiv ℝ m.field 0 x) = m.field ∧
      ContDiff ℝ 1 (fun x => m.field x - fderiv ℝ m.field 0 x) ∧
      (fun x => m.field x - fderiv ℝ m.field 0 x) 0 = 0 ∧
      fderiv ℝ (fun x => m.field x - fderiv ℝ m.field 0 x) 0 = 0 := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary
    (bautin_coeff2_pos h1 h0 hH) hH (m.sq_freq_of_isCriticalPair hcp)
  have hc : IsCritical (fderiv ℝ m.field 0) ω q p := IsCriticalPair.isCritical hcp rfl
  obtain ⟨K, β, hβ, hcen, hst⟩ := hc.exists_dichotomy hchar hr
  have hF := m.contDiff_field
  refine ⟨K, β, hβ, hcen, hst, hc.isCommutingProjection, by funext x; simp [fullField],
    hF.sub (fderiv ℝ m.field 0).contDiff, by simp [hcp.equilibrium], ?_⟩
  have hd := ((hF.differentiable one_ne_zero 0).hasFDerivAt.sub
    (fderiv ℝ m.field 0).hasFDerivAt).fderiv
  rw [show (fun x => m.field x - fderiv ℝ m.field 0 x) = m.field - ⇑(fderiv ℝ m.field 0)
    from rfl, hd, sub_self]

/-- **A degenerate Hopf point with `l₂ < 0` is locally asymptotically stable**: a model on the
Hopf boundary of the cubic (`a₁, a₀ > 0`, `a₂ a₁ = a₀`) with a critical pair `(q, p)`, a chart
`ι`, `π` of the critical plane with linear part `L₂` (`L₂² = −ω²`), an approximate centre
manifold `φ` of its field (`C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`, values in `ker critP`,
invariance defect `O(‖u‖⁵)` for `A = DF(0)`, `f = F − A`) and the quintic jet `J` of the chart
field of `φ` in the rotation coordinates of `L₂`, with `l₁(J) = 0` and `l₂(J) < 0`
(`Dynamics.CenterManifold.localAsymptoticStable_of_dichotomy_reduced_l2_neg` with the
dichotomy of `Dynamics.CenterManifold.IsCritical.exists_dichotomy`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg
    (m : Model) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    {ι : State 2 →L[ℝ] State 3} {π : State 3 →L[ℝ] State 2} (hc : IsChart (critP q p) ι π)
    {L₂ : State 2 →L[ℝ] State 2} (hrot : ∀ y, L₂ (L₂ y) = -(ω ^ 2) • y)
    {φ : State 3 → State 3}
    (hφ : ContDiffAt ℝ 1 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧ ∀ x, critP q p (φ x) = 0)
    (hdef : IsOrder (critP q p) (invarianceDefect (fderiv ℝ m.field 0) (critP q p)
      (fun x => m.field x - fderiv ℝ m.field 0 x) φ) 5)
    {J : Jet5}
    (hxy : ((fun u => frameX (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ ι π u) -
      (-ω * frameY L₂ ω u + Dynamics.Degenerate.poly3 J.F (frameX u) (frameY L₂ ω u) 0))
        =o[𝓝 0] fun u => ‖u‖ ^ 5) ∧
      ((fun u => frameY L₂ ω (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ ι π u) -
      (ω * frameX u + Dynamics.Degenerate.poly3 J.G (frameX u) (frameY L₂ ω u) 0))
        =o[𝓝 0] fun u => ‖u‖ ^ 5))
    (hl : J.l1 ω = 0 ∧ J.l2 ω < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨hφ, hφ0, hDφ, hφP⟩ := hφ
  obtain ⟨hx, hy⟩ := hxy
  obtain ⟨hl1, hl2⟩ := hl
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  obtain ⟨K, β, hβ, hcen, hst, hP, hFf, hf, hf0, hDf⟩ := bautin_reductionData m h1 h0 hH hcp
  rw [← hFf]
  exact localAsymptoticStable_of_dichotomy_reduced_l2_neg hP le_rfl (by linarith) hcen hst hf
    hf0 hDf hφ hφ0 hDφ hφP hdef hc hcp.freq_pos hrot hx hy hl1 hl2

/-- **A degenerate Hopf point with `l₂ > 0` is unstable** (hypotheses as
`mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`, `l₂(J) > 0`;
`Dynamics.CenterManifold.unstable_of_dichotomy_reduced_l2_pos`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_secondLyapunov_pos (m : Model)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    {ι : State 2 →L[ℝ] State 3} {π : State 3 →L[ℝ] State 2} (hc : IsChart (critP q p) ι π)
    {L₂ : State 2 →L[ℝ] State 2} (hrot : ∀ y, L₂ (L₂ y) = -(ω ^ 2) • y)
    {φ : State 3 → State 3}
    (hφ : ContDiffAt ℝ 1 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧ ∀ x, critP q p (φ x) = 0)
    (hdef : IsOrder (critP q p) (invarianceDefect (fderiv ℝ m.field 0) (critP q p)
      (fun x => m.field x - fderiv ℝ m.field 0 x) φ) 5)
    {J : Jet5}
    (hxy : ((fun u => frameX (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ ι π u) -
      (-ω * frameY L₂ ω u + Dynamics.Degenerate.poly3 J.F (frameX u) (frameY L₂ ω u) 0))
        =o[𝓝 0] fun u => ‖u‖ ^ 5) ∧
      ((fun u => frameY L₂ ω (chartField (fderiv ℝ m.field 0)
        (fun x => m.field x - fderiv ℝ m.field 0 x) φ ι π u) -
      (ω * frameX u + Dynamics.Degenerate.poly3 J.G (frameX u) (frameY L₂ ω u) 0))
        =o[𝓝 0] fun u => ‖u‖ ^ 5))
    (hl : J.l1 ω = 0 ∧ 0 < J.l2 ω) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨hφ, hφ0, hDφ, hφP⟩ := hφ
  obtain ⟨hx, hy⟩ := hxy
  obtain ⟨hl1, hl2⟩ := hl
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨K, β, hβ, hcen, hst, hP, hFf, hf, hf0, hDf⟩ := bautin_reductionData m h1 h0 hH hcp
  rw [← hFf]
  exact unstable_of_dichotomy_reduced_l2_pos hP le_rfl (by linarith) hcen hst hf hf0 hDf hφ hφ0
    hDφ hφP hdef hc hcp.freq_pos hrot hx hy hl1 hl2

end Degenerate

namespace Bautin

/-- The degenerate point `V = 6/5`, `K_p = 20` of the unit line. -/
def bpt : Model := unitLine (6 / 5) 20

/-- The reactive power at the point, `Q = −1/10`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_Q : bpt.Q = -1 / 10 := by
  change (unitLine (6 / 5) 20).g.qssReactive 0 = -1 / 10
  rw [Network.qssReactive_eq _ (by norm_num [unitLine, Network.absSq, Network.X])]
  norm_num [unitLine, Network.absSq, Network.X]

/-- The monic cubic at the point: `a₂ = 4`, `a₁ = 6`, `a₀ = 24`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_coeffs :
    bpt.g.coeff2 bpt.Q = 4 ∧ bpt.g.coeff1 bpt.Q = 6 ∧ bpt.g.coeff0 bpt.Q = 24 := by
  rw [bpt_Q]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X,
    bpt, unitLine]

/-- The operating point `(0, −1/10, 1/10)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_point :
    bpt.point = WithLp.toLp 2 ![0, -1 / 10, 1 / 10] := by
  ext i
  fin_cases i <;>
    simp [Model.point, qss, Network.is_re, Network.is_im, bpt, unitLine, Network.absSq, Network.X]
    <;> norm_num

/-- The linear part. -/
@[tmio M, powerlib_domain] theorem fderiv_field_zero :
    fderiv ℝ bpt.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
      !![-2, -20, 0; 0, -1, 1; 1, -1, -1] := by
  rw [show bpt.field = fun z => bpt.g.field (z + bpt.point) from rfl, fderiv_comp_add_right,
    zero_add, Model.fderiv_point, bpt.jac_eq (by norm_num [bpt, unitLine]), bpt_Q]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [bpt, unitLine]

/-- The linear part, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_apply (x : State 3) (i : Fin 3) :
    fderiv ℝ bpt.field 0 x i = ![-2 * x 0 - 20 * x 1, -x 1 + x 2, x 0 - x 1 - x 2] i := by
  rw [fderiv_field_zero, Dynamics.toEuclideanCLM_apply]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-- The nonlinear part. -/
def fnl (x : State 3) : State 3 := bpt.field x - fderiv ℝ bpt.field 0 x

/-- **The nonlinearities** of the translated field. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fnl_apply (x : State 3) (i : Fin 3) :
    fnl x i = ![2 * (Real.cos (x 0) - 1) - 20 * ((Real.cos (x 0) - 1) * x 1 +
      Real.sin (x 0) * x 2) - 2 * (Real.sin (x 0) - x 0), Real.cos (x 0) - 1,
      Real.sin (x 0) - x 0] i := by
  have hf : bpt.field x = bpt.g.field (x + bpt.point) := rfl
  rw [fnl, PiLp.sub_apply, hf, A_apply, bpt_point]
  fin_cases i <;>
    simp [PSC.field, bpt, unitLine, Network.power_eq, Network.rateD, Network.rateQ, Network.X] <;>
    ring


/-- `r = √6`, the Hopf frequency. -/
def r : ℝ := Real.sqrt 6

/-- `√6 > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem r_pos : 0 < r := Real.sqrt_pos.mpr (by norm_num)

/-- `(√6)² = 6`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem r_sq : r ^ 2 = 6 := Real.sq_sqrt (by norm_num)

/-- The right critical vector `q = (−4 + 2√6 i, 1, 1 + √6 i)`. -/
def qv : Fin 3 → ℂ := ![-4 + 2 * (r : ℂ) * I, 1, 1 + (r : ℂ) * I]

/-- The left critical vector `p`, `⟨p, q⟩ = 1`. -/
def pv3 : Fin 3 → ℂ :=
  ![-1 / 44 + (r : ℂ) / 66 * I, 4 / 11 + (r : ℂ) / 132 * I, 1 / 22 + 7 * (r : ℂ) / 132 * I]

/-- The point is an equilibrium. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpt_field_zero : bpt.field 0 = 0 := by
  ext i
  have h := fnl_apply 0 i
  rw [fnl, PiLp.sub_apply, map_zero] at h
  fin_cases i <;> simpa using h

/-- **The critical pair** `(q, p)` at `ω = √6`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCriticalPair_bpt :
    IsCriticalPair bpt.field 0 r qv pv3 := by
  have hJ : jacobianC bpt.field 0 = Linear.complexify !![-2, -20, 0; 0, -1, 1; 1, -1, -1] := by
    rw [jacobianC, fderiv_field_zero, cmat_toEuclideanCLM]
    rfl
  have hr : (r : ℂ) ^ 2 = 6 := by rw [← Complex.ofReal_pow, r_sq]; norm_num
  refine ⟨bpt_field_zero, r_pos, ?_, ?_, ?_⟩
  · rw [hJ]
    ext i
    fin_cases i <;> simp [qv, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring_nf <;>
      simp only [hr, Complex.I_sq] <;> ring_nf
  · rw [hJ]
    ext i
    fin_cases i <;> simp [pv3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring_nf <;>
      simp only [hr, Complex.I_sq] <;> ring_nf
  · simp [pv3, qv, dotProduct, Fin.sum_univ_three, map_ofNat, map_div₀, Complex.conj_ofReal,
      Complex.conj_I]
    ring_nf
    simp only [hr, Complex.I_sq]
    ring_nf


/-- The rational chart `ι' y = y₀ a + y₁ b`, `a = Re q = (−4, 1, 1)`, `b = Im q/√6 = (2, 0, 1)`. -/
def iotaR : State 2 →L[ℝ] State 3 :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (WithLp.toLp 2 ![-4, 1, 1] : State 3) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (WithLp.toLp 2 ![2, 0, 1] : State 3)

/-- The rational coordinates `π' x = (⟨(−1/22, 8/11, 1/11), x⟩, ⟨(2/11, 1/11, 7/11), x⟩)`. -/
def piR : State 3 →L[ℝ] State 2 :=
  (innerSL ℝ (WithLp.toLp 2 ![-1 / 22, 8 / 11, 1 / 11] : State 3)).smulRight
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (innerSL ℝ (WithLp.toLp 2 ![2 / 11, 1 / 11, 7 / 11] : State 3)).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The reduced linear part in the rational chart, `(y₀, y₁) ↦ (y₁, −6 y₀)`. -/
def rotR : State 2 →L[ℝ] State 2 :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (-6 : ℝ) • (EuclideanSpace.proj (0 : Fin 2)).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The stable eigenvector `w = (10, 1, −3)` (`A w = −4 w`), spanning `ker π'`. -/
def wv : State 3 := WithLp.toLp 2 ![10, 1, -3]

/-- The rational chart, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem iotaR_apply (y : State 2) (i : Fin 3) :
    iotaR y i = ![-4 * y 0 + 2 * y 1, y 0, y 0 + y 1] i := by
  fin_cases i <;> simp [iotaR]
  ring

/-- The rational coordinates, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_apply (x : State 3) :
    piR x 0 = -1 / 22 * x 0 + 8 / 11 * x 1 + 1 / 11 * x 2 ∧
      piR x 1 = 2 / 11 * x 0 + 1 / 11 * x 1 + 7 / 11 * x 2 := by
  simp only [piR, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp
  constructor <;> ring

/-- The reduced linear part, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem rotR_apply (y : State 2) :
    rotR y 0 = y 1 ∧ rotR y 1 = -6 * y 0 := by
  simp [rotR]

/-- `rotR² = −(√6)²`. Static evidence on the model. -/
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

/-- `A w = −4 w`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_wv : fderiv ℝ bpt.field 0 wv = (-4 : ℝ) • wv := by
  ext i; rw [A_apply]; fin_cases i <;> simp [wv] <;> norm_num

/-- `π' A ι' = rotR`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem piR_A_iotaR (y : State 2) :
    piR (fderiv ℝ bpt.field 0 (iotaR y)) = rotR y := by
  obtain ⟨h0, h1⟩ := piR_apply (fderiv ℝ bpt.field 0 (iotaR y))
  obtain ⟨r0, r1⟩ := rotR_apply y
  ext i; fin_cases i
  · simp only [Fin.zero_eta, h0, r0, A_apply, iotaR_apply]; simp; ring
  · simp only [Fin.mk_one, h1, r1, A_apply, iotaR_apply]; simp; ring

/-- **The rational chart is a chart of the critical plane**: `π' ι' = 1` and `ι' π' = critP q p`. -/
@[tmio M, powerlib_domain] theorem isChart_R : IsChart (critP qv pv3) iotaR piR := by
  refine ⟨piR_iotaR, fun x => ?_⟩
  obtain ⟨h0, h1⟩ := piR_apply x
  have hr : r ^ 2 = 6 := r_sq
  rw [critP, ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1]
  ext i
  rw [iotaR_apply]
  fin_cases i <;>
    simp [h0, h1, qv, pv3, reV_apply, imV_apply, PiLp.inner_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp only [hr] <;> ring_nf

/-- **`(1 − P) v = (v₁ − (π' v)₀) w`**: the stable component of a vector. -/
@[tmio M, powerlib_domain] theorem sub_iotaR_piR (v : State 3) :
    v - iotaR (piR v) = (v 1 - piR v 0) • wv := by
  obtain ⟨h0, h1⟩ := piR_apply v
  ext i
  fin_cases i <;> simp [iotaR_apply, h0, h1, wv] <;> ring

/-! ## The approximate centre manifold -/

/-- `h` of the manifold, degree 2. -/
def hL2 : List (ℝ × ℕ × ℕ × ℕ) := [(-17 / 55, 2, 0, 0), (-18 / 55, 1, 1, 0), (-61 / 110, 0, 2, 0)]

/-- `10 h`, the angle part of the manifold, degree 2. -/
def aL2 : List (ℝ × ℕ × ℕ × ℕ) := [(-34 / 11, 2, 0, 0), (-36 / 11, 1, 1, 0), (-61 / 11, 0, 2, 0)]

/-- `−3 h`, the `i_q` part of the manifold, degree 2. -/
def cL2 : List (ℝ × ℕ × ℕ × ℕ) := [(51 / 55, 2, 0, 0), (54 / 55, 1, 1, 0), (183 / 110, 0, 2, 0)]

/-- `h` of the manifold, degree 3. -/
def hL3 : List (ℝ × ℕ × ℕ × ℕ) := [(50672 / 12705, 3, 0, 0), (7594 / 4235, 2, 1, 0), (1238 / 4235,
    1, 2, 0), (-9199 / 12705, 0, 3, 0)]

/-- `10 h`, the angle part of the manifold, degree 3. -/
def aL3 : List (ℝ × ℕ × ℕ × ℕ) := [(101344 / 2541, 3, 0, 0), (15188 / 847, 2, 1, 0), (2476 / 847, 1,
    2, 0), (-18398 / 2541, 0, 3, 0)]

/-- `−3 h`, the `i_q` part of the manifold, degree 3. -/
def cL3 : List (ℝ × ℕ × ℕ × ℕ) := [(-50672 / 4235, 3, 0, 0), (-22782 / 4235, 2, 1, 0), (-3714 /
    4235, 1, 2, 0), (9199 / 4235, 0, 3, 0)]

/-- `h` of the manifold, degree 4. -/
def hL4 : List (ℝ × ℕ × ℕ × ℕ) := [(171649 / 3993, 4, 0, 0), (487064 / 27951, 3, 1, 0), (217619 /
    9317, 2, 2, 0), (205036 / 27951, 1, 3, 0), (-12253 / 111804, 0, 4, 0)]

/-- `10 h`, the angle part of the manifold, degree 4. -/
def aL4 : List (ℝ × ℕ × ℕ × ℕ) := [(1716490 / 3993, 4, 0, 0), (4870640 / 27951, 3, 1, 0), (2176190 /
    9317, 2, 2, 0), (2050360 / 27951, 1, 3, 0), (-61265 / 55902, 0, 4, 0)]

/-- `−3 h`, the `i_q` part of the manifold, degree 4. -/
def cL4 : List (ℝ × ℕ × ℕ × ℕ) := [(-171649 / 1331, 4, 0, 0), (-487064 / 9317, 3, 1, 0), (-652857 /
    9317, 2, 2, 0), (-205036 / 9317, 1, 3, 0), (12253 / 37268, 0, 4, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low1L4 : List (ℝ × ℕ × ℕ × ℕ) := [(80, 2, 0, 0), (40, 1, 1, 0), (-40, 0, 2, 0), (296, 3, 0, 0),
    (96 / 11, 2, 1, 0), (3412 / 11, 1, 2, 0), (488 / 11, 0, 3, 0), (-1450968 / 847, 4, 0, 0), (-8192
    / 11, 3, 1, 0), (357328 / 847, 2, 2, 0), (197744 / 847, 1, 3, 0), (209142 / 847, 0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low1L5 : List (ℝ × ℕ × ℕ × ℕ) := [(-222051504 / 9317, 5, 0, 0), (-34199680 / 2541, 4, 1, 0),
    (-39613360 / 2541, 3, 2, 0), (-41946400 / 9317, 2, 3, 0), (-3437180 / 27951, 1, 4, 0), (11381056
    / 27951, 0, 5, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low2L4 : List (ℝ × ℕ × ℕ × ℕ) := [(-8, 2, 0, 0), (8, 1, 1, 0), (-2, 0, 2, 0), (-136 / 11, 3, 0,
    0), (-76 / 11, 2, 1, 0), (-172 / 11, 1, 2, 0), (122 / 11, 0, 3, 0), (140114 / 847, 4, 0, 0),
    (-33448 / 847, 3, 1, 0), (-25974 / 847, 2, 2, 0), (-49372 / 847, 1, 3, 0), (-387 / 1694, 0, 4,
    0)]

/-- The weight-five truncation, degree five. -/
def low2L5 : List (ℝ × ℕ × ℕ × ℕ) := [(52428952 / 27951, 5, 0, 0), (80900 / 9317, 4, 1, 0),
    (25328720 / 27951, 3, 2, 0), (-4297820 / 27951, 2, 3, 0), (-157830 / 1331, 1, 4, 0), (-1267681 /
    27951, 0, 5, 0)]

/-- The weight-five truncation, degrees two to four. -/
def low3L4 : List (ℝ × ℕ × ℕ × ℕ) := [(32 / 3, 3, 0, 0), (-16, 2, 1, 0), (8, 1, 2, 0), (-4 / 3, 0,
    3, 0), (272 / 11, 4, 0, 0), (16 / 11, 3, 1, 0), (268 / 11, 2, 2, 0), (-416 / 11, 1, 3, 0), (122
    / 11, 0, 4, 0)]

/-- The weight-five truncation, degree five. -/
def low3L5 : List (ℝ × ℕ × ℕ × ℕ) := [(-1306472 / 4235, 5, 0, 0), (192996 / 847, 4, 1, 0), (75144 /
    847, 3, 2, 0), (70908 / 847, 2, 3, 0), (-34922 / 847, 1, 4, 0), (-67779 / 4235, 0, 5, 0)]

/-- The jet of the first chart coordinate, degree 2. -/
def cF2 : List (ℝ × ℕ × ℕ × ℕ) := [(-96 / 11, 2, 0, 0), (36 / 11, 1, 1, 0), (6 / 11, 0, 2, 0)]

/-- The jet of the second chart coordinate, degree 2. -/
def cG2 : List (ℝ × ℕ × ℕ × ℕ) := [(120 / 11, 2, 0, 0), (120 / 11, 1, 1, 0), (-90 / 11, 0, 2, 0)]

/-- The jet of the first chart coordinate, degree 3. -/
def cF3 : List (ℝ × ℕ × ℕ × ℕ) := [(-7036 / 363, 3, 0, 0), (-932 / 121, 2, 1, 0), (-2734 / 121, 1,
    2, 0), (1742 / 363, 0, 3, 0)]

/-- The jet of the second chart coordinate, degree 3. -/
def cG3 : List (ℝ × ℕ × ℕ × ℕ) := [(6184 / 121, 3, 0, 0), (-716 / 121, 2, 1, 0), (6228 / 121, 1, 2,
    0), (1542 / 121, 0, 3, 0)]

/-- The jet of the first chart coordinate, degree 4. -/
def cF4 : List (ℝ × ℕ × ℕ × ℕ) := [(1748170 / 9317, 4, 0, 0), (11960 / 1331, 3, 1, 0), (-319210 /
    9317, 2, 2, 0), (-508540 / 9317, 1, 3, 0), (-174275 / 18634, 0, 4, 0)]

/-- The jet of the second chart coordinate, degree 4. -/
def cG4 : List (ℝ × ℕ × ℕ × ℕ) := [(-2138534 / 9317, 4, 0, 0), (-1425112 / 9317, 3, 1, 0), (646694 /
    9317, 2, 2, 0), (52532 / 9317, 1, 3, 0), (890997 / 18634, 0, 4, 0)]

/-- The jet of the first chart coordinate, degree 5. -/
def cF5 : List (ℝ × ℕ × ℕ × ℕ) := [(3414172448 / 1537305, 5, 0, 0), (202534876 / 307461, 4, 1, 0),
    (133378008 / 102487, 3, 2, 0), (37514788 / 307461, 2, 3, 0), (-23787272 / 307461, 1, 4, 0),
    (-3680709 / 73205, 0, 5, 0)]

/-- The jet of the second chart coordinate, degree 5. -/
def cG5 : List (ℝ × ℕ × ℕ × ℕ) := [(-5480162048 / 1537305, 5, 0, 0), (-732072856 / 307461, 4, 1, 0),
    (-245803688 / 102487, 3, 2, 0), (-266147608 / 307461, 2, 3, 0), (-26903788 / 307461, 1, 4, 0),
    (25136138 / 512435, 0, 5, 0)]

/-- The polynomial part of the defect, degrees five to eight. -/
def highD : List (ℝ × ℕ × ℕ × ℕ) := [(-2230368464 / 1537305, 5, 0, 0), (204097352 / 307461, 4, 1,
    0), (42578288 / 307461, 3, 2, 0), (3195356 / 307461, 2, 3, 0), (-70437844 / 307461, 1, 4, 0),
    (-28733048 / 1537305, 0, 5, 0), (-24780214864 / 10146213, 6, 0, 0), (-25791008 / 483153, 5, 1,
    0), (-11661868520 / 3382071, 4, 2, 0), (16394794000 / 10146213, 3, 3, 0), (2940626620 / 3382071,
    2, 4, 0), (1069801024 / 3382071, 1, 5, 0), (300490334 / 10146213, 0, 6, 0)]

/-- `h`, degrees two to four. -/
def hL : List (ℝ × ℕ × ℕ × ℕ) := hL2 ++ hL3 ++ hL4

/-- The graph in chart coordinates, `H(y) = h(y) w`. -/
def manifoldH (y : State 2) : State 3 := poly3 hL (y 0) (y 1) 0 • wv

/-- **The order-four approximate centre manifold** `φ(x) = H(π' x)`. -/
def manifold (x : State 3) : State 3 := manifoldH (piR x)

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

/-- `φ` is `C¹`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem contDiffAt_manifold : ContDiffAt ℝ 1 manifold 0 := by
  have h1 := Dynamics.Degenerate.contDiff_poly3 hL ((Dynamics.coord 0).comp piR)
    ((Dynamics.coord 1).comp piR) 0 (k := 1)
  have e : manifold = fun x => poly3 hL ((Dynamics.coord 0).comp piR x)
      ((Dynamics.coord 1).comp piR x) ((0 : State 3 →L[ℝ] ℝ) x) • wv := by
    funext x; simp [manifold, manifoldH]
  rw [e]
  exact (h1.smul contDiff_const).contDiffAt

/-- `φ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem manifold_zero : manifold 0 = 0 := by
  simp [manifold, manifoldH, hL, hL2, hL3, hL4]

/-- `Dφ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fderiv_manifold_zero : fderiv ℝ manifold 0 = 0 := by
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldH (piR 0)
  have hc : HasFDerivAt manifold (L.comp piR) 0 := hL'.comp (0 : State 3) piR.hasFDerivAt
  rw [hc.fderiv]
  ext v i
  simp [hLv, hL, hL2, hL3, hL4]

/-- `φ` takes values in `ker P`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critP_manifold (x : State 3) :
    critP qv pv3 (manifold x) = 0 := by
  rw [← isChart_R.ι_π, manifold, piR_manifoldH, map_zero]

/-! ## The chart field -/

/-- The point `ι' y + H(y)` of the manifold over `y`. -/
def chartPt (y : State 2) : State 3 := iotaR y + manifoldH y

/-- **The chart field** of the manifold: `rotR y + π' f(ι' y + H y)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem chartField_eq (y : State 2) :
    chartField (fderiv ℝ bpt.field 0) fnl manifold iotaR piR y =
      rotR y + piR (fnl (chartPt y)) := by
  rw [chartField, manifold, piR_iotaR, map_add, piR_A_iotaR]
  rfl

/-- The linear part of the angle over `y`. -/
def lin0 (y : State 2) : ℝ := -4 * y 0 + 2 * y 1

/-- The linear part of `i_d` over `y`. -/
def lin1 (y : State 2) : ℝ := y 0

/-- The linear part of `i_q` over `y`. -/
def lin2 (y : State 2) : ℝ := y 0 + y 1

/-- A planar polynomial at `y`. -/
def pv (L : List (ℝ × ℕ × ℕ × ℕ)) (y : State 2) : ℝ := poly3 L (y 0) (y 1) 0

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

/-- The first chart coordinate of `f` on the manifold. -/
def G0 (y : State 2) : ℝ := piR (fnl (chartPt y)) 0

/-- The second chart coordinate of `f` on the manifold. -/
def G1 (y : State 2) : ℝ := piR (fnl (chartPt y)) 1

/-- The droop nonlinearity `−20((cos x₀ − 1) x₁ + sin x₀ · x₂)` on the manifold. -/
def f0v (y : State 2) : ℝ :=
  -20 * ((Real.cos (tv y) - 1) * x1v y + Real.sin (tv y) * x2v y)

/-- The chart coordinates of `f` on the manifold. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem G_eq (y : State 2) :
    G0 y = -1 / 22 * f0v y + 7 / 11 * (Real.cos (tv y) - 1) +
        2 / 11 * (Real.sin (tv y) - tv y) ∧
      G1 y = 2 / 11 * f0v y + 5 / 11 * (Real.cos (tv y) - 1) +
        3 / 11 * (Real.sin (tv y) - tv y) := by
  obtain ⟨c0, c1, c2⟩ := chartPt_apply y
  obtain ⟨g0, g1⟩ := piR_apply (fnl (chartPt y))
  simp only [G0, G1, g0, g1, fnl_apply, f0v]
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

/-- The weight-five part of `−20((C₄(u) − 1) x₁ + S₅(u) x₂)` in the pieces of `u`, `x₁`, `x₂`
(`C₄`, `S₅` the Taylor polynomials of `cos`, `sin`). -/
def lowF1 (l0 a2 a3 a4 l1 b2 b3 l2 c2 c3 c4 : ℝ) : ℝ :=
  -20 * (-((l0 ^ 2 + 2 * l0 * a2 + 2 * l0 * a3 + a2 ^ 2) * l1 +
    (l0 ^ 2 + 2 * l0 * a2) * b2 + l0 ^ 2 * b3) / 2 + l0 ^ 4 * l1 / 24 +
    (l0 * l2 + l0 * c2 + a2 * l2 + l0 * c3 + a2 * c2 + a3 * l2 + l0 * c4 + a2 * c3 + a3 * c2 +
      a4 * l2) - ((l0 ^ 3 + 3 * l0 ^ 2 * a2) * l2 + l0 ^ 3 * c2) / 6)

/-- The weight-five part of `C₄(u) − 1`. -/
def lowF2 (l0 a2 a3 a4 : ℝ) : ℝ :=
  -(l0 ^ 2 + 2 * l0 * a2 + 2 * l0 * a3 + 2 * l0 * a4 + a2 ^ 2 + 2 * a2 * a3) / 2 +
    (l0 ^ 4 + 4 * l0 ^ 3 * a2) / 24

/-- The weight-five part of `S₅(u) − u`. -/
def lowF3 (l0 a2 a3 : ℝ) : ℝ :=
  -(l0 ^ 3 + 3 * l0 ^ 2 * a2 + 3 * l0 ^ 2 * a3 + 3 * l0 * a2 ^ 2) / 6 + l0 ^ 5 / 120

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
    pv cF y = -1 / 22 * pv low1L y + 7 / 11 * pv low2L y + 2 / 11 * pv low3L y := by
  simp only [pv, cF, cF2, cF3, cF4, cF5, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L,
    low3L4, low3L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The jet of the second chart coordinate from the truncated nonlinearities. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem cG_eq (y : State 2) :
    pv cG y = 2 / 11 * pv low1L y + 5 / 11 * pv low2L y + 3 / 11 * pv low3L y := by
  simp only [pv, cG, cG2, cG3, cG4, cG5, low1L, low1L4, low1L5, low2L, low2L4, low2L5, low3L,
    low3L4, low3L5, poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- **The first chart coordinate has the jet `cF`**: `G₀ − cF = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G0_sub_jet :
    (fun y => G0 y - pv cF y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((f1_sub_low.const_mul_left (-1 / 22)).add
    (f2_sub_low.const_mul_left (7 / 11))).add
      (f3_sub_low.const_mul_left (2 / 11))).congr_left fun y => ?_
  rw [(G_eq y).1, cF_eq]
  ring

/-- **The second chart coordinate has the jet `cG`**: `G₁ − cG = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G1_sub_jet :
    (fun y => G1 y - pv cG y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((f1_sub_low.const_mul_left (2 / 11)).add
    (f2_sub_low.const_mul_left (5 / 11))).add
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

/-- **The invariance defect at a chart point** is `d(y) w`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem defect_eq (y : State 2) :
    invarianceDefect (fderiv ℝ bpt.field 0) (critP qv pv3) fnl manifold (iotaR y) =
      dcomp y • wv := by
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldH y
  have hdef := invarianceDefect_comp_chart (A := fderiv ℝ bpt.field 0) (f := fnl) isChart_R
    hL'.differentiableAt
  rw [show (fun x => manifoldH (piR x)) = manifold from rfl, hL'.fderiv] at hdef
  rw [hdef, chartField_eq, hLv]
  have hφ : manifold (iotaR y) = manifoldH y := by rw [manifold, piR_iotaR]
  have hP : ∀ v, critP qv pv3 v = iotaR (piR v) := fun v => (isChart_R.ι_π v).symm
  have hN : normalField (fderiv ℝ bpt.field 0) (critP qv pv3) fnl manifold (iotaR y) =
      (-4 * pv hL y + (Real.cos (tv y) - 1 - G0 y)) • wv := by
    rw [normalField, hφ]
    simp only [_root_.sub_apply, one_apply_eq_self, hP]
    have hA : fderiv ℝ bpt.field 0 (manifoldH y) = (-4 * pv hL y) • wv := by
      rw [manifoldH, map_smul, A_wv, smul_smul, pv, mul_comm]
    rw [hA, map_smul, piR_wv, smul_zero, map_zero, sub_zero, show iotaR y + manifoldH y =
      chartPt y from rfl, sub_iotaR_piR]
    obtain ⟨c0, -, -⟩ := chartPt_apply y
    rw [fnl_apply, c0, add_smul]
    rfl
  rw [hN, ← sub_smul]
  obtain ⟨r0, r1⟩ := rotR_apply y
  congr 1
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
    IsOrder (critP qv pv3) (invarianceDefect (fderiv ℝ bpt.field 0) (critP qv pv3) fnl manifold)
      5 := by
  have h := isChart_R.isOrder_of_isBigO (k := 5)
    (G := invarianceDefect (fderiv ℝ bpt.field 0) (critP qv pv3) fnl manifold) ?_
  · exact_mod_cast h
  have h2 : (fun y : State 2 => dcomp y • wv) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (IsBigO.of_bound ‖wv‖ (Eventually.of_forall fun y => by
      rw [norm_smul, mul_comm])).trans dcomp_isBigO
  exact h2.congr_left fun y => (defect_eq y).symm

/-! ## The jet in the rotation frame and the second Lyapunov coefficient -/

/-- The normalised jet `J/ω` (`τ = ωt`, `ω = √6`). -/
def jetN : Jet5 where
  a20 := (-16 / 11 * r)
  a11 := (-36 / 11)
  a02 := (6 / 11 * r)
  b20 := (-20 / 11)
  b11 := (20 / 11 * r)
  b02 := (90 / 11)
  a30 := (-3518 / 1089 * r)
  a21 := (932 / 121)
  a12 := (-2734 / 121 * r)
  a03 := (-3484 / 121)
  b30 := (-3092 / 363)
  b21 := (-358 / 363 * r)
  b12 := (-6228 / 121)
  b03 := (1542 / 121 * r)
  a40 := (874085 / 27951 * r)
  a31 := (-11960 / 1331)
  a22 := (-319210 / 9317 * r)
  a13 := (3051240 / 9317)
  a04 := (-522825 / 9317 * r)
  b40 := (1069267 / 27951)
  b31 := (-712556 / 27951 * r)
  b22 := (-646694 / 9317)
  b13 := (52532 / 9317 * r)
  b04 := (-2672991 / 9317)
  a50 := (1707086224 / 4611915 * r)
  a41 := (-202534876 / 307461)
  a32 := (133378008 / 102487 * r)
  a23 := (-75029576 / 102487)
  a14 := (-47574544 / 102487 * r)
  a05 := (132505524 / 73205)
  b50 := (2740081024 / 4611915)
  b41 := (-366036428 / 922383 * r)
  b32 := (245803688 / 102487)
  b23 := (-266147608 / 307461 * r)
  b14 := (53807576 / 102487)
  b05 := (150816828 / 512435 * r)

/-- The quintic jet of the chart field in the rotation coordinates of `rotR`. -/
def jet : Jet5 where
  a20 := r * (-16 / 11 * r)
  a11 := r * (-36 / 11)
  a02 := r * (6 / 11 * r)
  b20 := r * (-20 / 11)
  b11 := r * (20 / 11 * r)
  b02 := r * (90 / 11)
  a30 := r * (-3518 / 1089 * r)
  a21 := r * (932 / 121)
  a12 := r * (-2734 / 121 * r)
  a03 := r * (-3484 / 121)
  b30 := r * (-3092 / 363)
  b21 := r * (-358 / 363 * r)
  b12 := r * (-6228 / 121)
  b03 := r * (1542 / 121 * r)
  a40 := r * (874085 / 27951 * r)
  a31 := r * (-11960 / 1331)
  a22 := r * (-319210 / 9317 * r)
  a13 := r * (3051240 / 9317)
  a04 := r * (-522825 / 9317 * r)
  b40 := r * (1069267 / 27951)
  b31 := r * (-712556 / 27951 * r)
  b22 := r * (-646694 / 9317)
  b13 := r * (52532 / 9317 * r)
  b04 := r * (-2672991 / 9317)
  a50 := r * (1707086224 / 4611915 * r)
  a41 := r * (-202534876 / 307461)
  a32 := r * (133378008 / 102487 * r)
  a23 := r * (-75029576 / 102487)
  a14 := r * (-47574544 / 102487 * r)
  a05 := r * (132505524 / 73205)
  b50 := r * (2740081024 / 4611915)
  b41 := r * (-366036428 / 922383 * r)
  b32 := r * (245803688 / 102487)
  b23 := r * (-266147608 / 307461 * r)
  b14 := r * (53807576 / 102487)
  b05 := r * (150816828 / 512435 * r)

/-- The second rotation coordinate of `rotR`, `−y₁/√6`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem frameY_rotR (u : State 2) :
    frameY rotR r u = -r⁻¹ * u 1 := by
  rw [PlanarFocus.frameY_apply, (rotR_apply u).1]

/-- The jet in the rotation frame is the chart jet: `F_J(a, Y) = cF(a, −√6 Y)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem jetF_frame (a Y : ℝ) :
    poly3 jet.F a Y 0 = poly3 cF a (-(r * Y)) 0 := by
  simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4,
    PlanarFocus.Jet5.F5, jet, cF, cF2, cF3, cF4, cF5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  linear_combination (1707086224*a ^ 5/4611915 + 874085*a ^ 4/27951 - 3518*a ^ 3/1089 + 37514788*a ^
    2*Y ^ 3*r/307461 - 16*a ^ 2/11 + 23787272*a*Y ^ 4*r ^ 2/307461 - 508540*a*Y ^ 3*r/9317 -
    3680709*Y ^ 5*r ^ 3/73205 - 22084254*Y ^ 5*r/73205 + 174275*Y ^ 4*r ^ 2/18634 + 1742*Y ^
    3*r/363) * r_sq

/-- The jet in the rotation frame is the chart jet: `√6 G_J(a, Y) = −cG(a, −√6 Y)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem jetG_frame (a Y : ℝ) :
    r * poly3 jet.G a Y 0 = -poly3 cG a (-(r * Y)) 0 := by
  simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet.G2, PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4,
    PlanarFocus.Jet5.G5, jet, cG, cG2, cG3, cG4, cG5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]
  linear_combination (2740081024*a ^ 5/4611915 - 366036428*a ^ 4*Y*r/922383 + 1069267*a ^ 4/27951 -
    712556*a ^ 3*Y*r/27951 - 3092*a ^ 3/363 - 358*a ^ 2*Y*r/363 - 20*a ^ 2/11 - 26903788*a*Y ^ 4*r ^
    2/307461 + 20*a*Y*r/11 - 25136138*Y ^ 5*r ^ 3/512435 + 890997*Y ^ 4*r ^ 2/18634) * r_sq

/-- The normalised jet (`τ = √6 t`): `J/√6 = jetN`. -/
@[tmio M, powerlib_domain] theorem jet_nrm : jet.nrm r = jetN := by
  have h : r ≠ 0 := r_pos.ne'
  simp only [PlanarFocus.Jet5.nrm, jet, jetN, mul_div_cancel_left₀ _ h]

/-- The Lyapunov chain of the normalised jet: `c30` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c30 : jetN.c30 1 = (248 / 33) := by
  simp only [PlanarFocus.Jet.c30]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c21` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c21 : jetN.c21 1 = (32 / 11 * r) := by
  simp only [PlanarFocus.Jet.c21]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c12` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c12 : jetN.c12 1 = (180 / 11) := by
  simp only [PlanarFocus.Jet.c12]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `c03` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c03 : jetN.c03 1 = (4 / 11 * r) := by
  simp only [PlanarFocus.Jet.c03]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `d40` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d40 : jetN.d40 1 = (-52 / 3) := by
  simp only [PlanarFocus.Jet.d40]
  simp only [jetN]
  linear_combination (60/121) * r_sq

/-- The Lyapunov chain of the normalised jet: `d31` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d31 : jetN.d31 1 = (48508 / 1089 * r) := by
  simp only [PlanarFocus.Jet.d31]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `d22` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d22 : jetN.d22 1 = (5120 / 121) := by
  simp only [PlanarFocus.Jet.d22]
  simp only [jetN]
  linear_combination (312/121) * r_sq

/-- The Lyapunov chain of the normalised jet: `d13` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d13 : jetN.d13 1 = (5244 / 121 * r) := by
  simp only [PlanarFocus.Jet.d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `l1` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l1 : jetN.l1 1 = (0) := by
  simp only [PlanarFocus.Jet.l1]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r50 : jetN.r50 1 = (-425078 / 27951 * r) := by
  simp only [PlanarFocus.Jet5.r50]
  rw [jv_c30, jv_c21, jv_d40, jv_d31]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r41 : jetN.r41 1 = (-21908650 / 27951) := by
  simp only [PlanarFocus.Jet5.r41]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22]
  simp only [jetN]
  linear_combination (-539248/3993) * r_sq

/-- The Lyapunov chain of the normalised jet: `r32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r32 : jetN.r32 1 = (-4570396 / 3993 * r) := by
  simp only [PlanarFocus.Jet5.r32]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r23 : jetN.r23 1 = (-3459756 / 9317) := by
  simp only [PlanarFocus.Jet5.r23]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (200688/1331) * r_sq

/-- The Lyapunov chain of the normalised jet: `r14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r14 : jetN.r14 1 = (6436182 / 9317 * r) := by
  simp only [PlanarFocus.Jet5.r14]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r05 : jetN.r05 1 = (-7637166 / 9317) := by
  simp only [PlanarFocus.Jet5.r05]
  rw [jv_c12, jv_c03, jv_d13]
  simp only [jetN]
  linear_combination (49968/1331) * r_sq

/-- The Lyapunov chain of the normalised jet: `e50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e50 : jetN.e50 1 = (-17985098 / 27951) := by
  simp only [PlanarFocus.Jet5.e50]
  rw [jv_r41, jv_r23, jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e41 : jetN.e41 1 = (425078 / 27951 * r) := by
  simp only [PlanarFocus.Jet5.e41]
  rw [jv_r50]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e32 : jetN.e32 1 = (-11336140 / 9317) := by
  simp only [PlanarFocus.Jet5.e32]
  rw [jv_r23, jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e23 : jetN.e23 1 = (3743676 / 9317 * r) := by
  simp only [PlanarFocus.Jet5.e23]
  rw [jv_r50, jv_r32]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e14 : jetN.e14 1 = (-7637166 / 9317) := by
  simp only [PlanarFocus.Jet5.e14]
  rw [jv_r05]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `e05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e05 : jetN.e05 1 = (210234 / 9317 * r) := by
  simp only [PlanarFocus.Jet5.e05]
  rw [jv_r50, jv_r32, jv_r14]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r60 : jetN.r60 1 = (9305581456 / 1537305 * r) := by
  simp only [PlanarFocus.Jet5.r60]
  rw [jv_c30, jv_c21, jv_d40, jv_d31, jv_e50, jv_e41]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r51 : jetN.r51 1 = (7937038424 / 658845) := by
  simp only [PlanarFocus.Jet5.r51]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22, jv_e50, jv_e41, jv_e32]
  simp only [jetN]
  linear_combination (-395397704/922383) * r_sq

/-- The Lyapunov chain of the normalised jet: `r42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r42 : jetN.r42 1 = (-1167068944 / 307461 * r) := by
  simp only [PlanarFocus.Jet5.r42]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e50, jv_e41, jv_e32,
    jv_e23]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r33 : jetN.r33 1 = (-2048073488 / 307461) := by
  simp only [PlanarFocus.Jet5.r33]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e41, jv_e32, jv_e23,
    jv_e14]
  simp only [jetN]
  linear_combination (-576410224/307461) * r_sq

/-- The Lyapunov chain of the normalised jet: `r24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r24 : jetN.r24 1 = (-1442829760 / 102487 * r) := by
  simp only [PlanarFocus.Jet5.r24]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13, jv_e32, jv_e23, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `r15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r15 : jetN.r15 1 = (-10215930264 / 512435) := by
  simp only [PlanarFocus.Jet5.r15]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13, jv_e23, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (102568632/102487) * r_sq

/-- The Lyapunov chain of the normalised jet: `r06` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r06 : jetN.r06 1 = (-724830144 / 512435 * r) := by
  simp only [PlanarFocus.Jet5.r06]
  rw [jv_c12, jv_c03, jv_d13, jv_e14, jv_e05]
  simp only [jetN]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f60 : jetN.f60 1 = (-25872327284 / 13835745) := by
  simp only [PlanarFocus.Jet5.f60]
  rw [jv_r51, jv_r33, jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f51 : jetN.f51 1 = (-8794477456 / 1537305 * r) := by
  simp only [PlanarFocus.Jet5.f51]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f42 : jetN.f42 1 = (-17883987256 / 1537305) := by
  simp only [PlanarFocus.Jet5.f42]
  rw [jv_r33, jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f33 : jetN.f33 1 = (-2440248704 / 307461 * r) := by
  simp only [PlanarFocus.Jet5.f33]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f24 : jetN.f24 1 = (-5107965132 / 512435) := by
  simp only [PlanarFocus.Jet5.f24]
  rw [jv_r15]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `f15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f15 : jetN.f15 1 = (-895198144 / 512435 * r) := by
  simp only [PlanarFocus.Jet5.f15]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `k6` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_k6 : jetN.k6 1 = (25600 / 77 * r) := by
  simp only [PlanarFocus.Jet5.k6]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  linear_combination (0) * r_sq

/-- The Lyapunov chain of the normalised jet: `l2` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l2 : jetN.l2 1 = (51200 / 77 * r) := by
  simp only [PlanarFocus.Jet5.l2]
  rw [jv_k6]
  linear_combination (0) * r_sq

/-- `l₁(J) = 0` at the degenerate point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1_eq_zero : jet.l1 r = 0 := by
  rw [← PlanarFocus.Jet5.l1_nrm jet r r_pos.ne', jet_nrm, jv_l1]

/-- **`l₂(J) = 51200√6/77 > 0` at the degenerate point.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l2_eq : jet.l2 r = 51200 / 77 * r := by
  rw [← PlanarFocus.Jet5.l2_nrm jet r r_pos.ne', jet_nrm, jv_l2]

end Bautin

open Bautin in
/-- **The degenerate Hopf point of the unit line is unstable**: at `V = 6/5`, `K_p = 20`
(`ℓ₁ = 0`, `Line.PSC.unitLine_bautin_firstLyapunov`) the model is a weak focus of the second
order with `l₂ = 51200√6/77 > 0` in the rotation frame of the rational chart `ι'`, `π'` of the
critical plane (the approximate centre manifold `Bautin.manifold`, invariance defect `O(‖u‖⁵)`,
the quintic jet `Bautin.jet`; `mem_den_unstable_of_secondLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem unitLine_bautin_mem_den_unstable :
    connection% (unitLine (6 / 5) 20 ∈ family.den (.flow .unstable)) := by
  obtain ⟨h2, h1, h0⟩ := bpt_coeffs
  have hr0 : r ≠ 0 := r_pos.ne'
  refine mem_den_unstable_of_secondLyapunov_pos bpt (by rw [h1]; norm_num)
    (by rw [h0]; norm_num) (by rw [h2, h1, h0]; norm_num) isCriticalPair_bpt isChart_R rotR_rotR
    ⟨contDiffAt_manifold, manifold_zero, fderiv_manifold_zero, critP_manifold⟩ isOrder_defect
    (J := jet) ⟨?_, ?_⟩
    ⟨jet_l1_eq_zero, by rw [jet_l2_eq]; exact mul_pos (by norm_num) r_pos⟩
  · refine (G0_sub_jet.trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => bpt.field x - fderiv ℝ bpt.field 0 x) = fnl from rfl, chartField_eq,
      frameY_rotR, jetF_frame, show -(r * (-r⁻¹ * y 1)) = y 1 by field_simp]
    simp only [PlanarFocus.frameX_apply, PiLp.add_apply, (rotR_apply y).1, G0, pv]
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
    simp only [PiLp.add_apply, (rotR_apply y).2, G1, pv]
    have h6 : (6 : ℝ) = r ^ 2 := r_sq.symm
    field_simp
    rw [h6]
    ring

end PSC
end powerlib.GFM.Line
