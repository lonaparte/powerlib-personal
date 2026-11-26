import theorem.GridTiedConverter.GFM.QVDroopHopf
import theorem.Dynamics.CenterReductionBautin
import theorem.Dynamics.CenterManifoldChart
import theorem.Dynamics.PolySign

/-! # Grid-forming converter with Q–V droop: a path of Hopf points and its Bautin point

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged (state `(δ, Δω, Q_f)`,
  quasi-static line, export-positive powers, `E = E₀ − n_q (Q_f − Q_ref)`), read about a selected
  point on `QVDroop.family`. Excluded as there.
* The family laws: a Hopf point of `theorem/GridTiedConverter/GFM/QVDroopHopf.lean`
  (`Model.IsHopf`: `A > 0`, `C > 0`, `G = 0`; `M, D, ω_q > 0`, `E* ≠ 0`) with a critical pair at
  its frequency, read in any chart `ι`, `π` of the critical plane with a linear part `L₂`,
  `L₂² = −ω²`.
* The path `QVDroop.Bautin.bpath μ`, `μ > 0`: `M = 85/122`, `D = 10/61`, `ω_q = 1`, `n_q = μ`,
  `E₀ = 1`, `V = 10μ/(2 + 5μ)`, `R = 8μ/(2 + 5μ)`, `X = 4μ/(2 + 5μ)`,
  `P_ref = (2 − 5μ)/(10μ)`, `Q_ref = Q_f* = (2 − 5μ)/(20μ)`, at `δ* = 0` (EMF `E* = 1`). Along
  the path the Jacobian is fixed (`P_δ = 1/2`, `n_q P_E = 2/5`, `Q_δ = −1`, `K = 6/5`; `A = C = 1`,
  `G = 0`, frequency `ω = 1`, `det(sI − J) = (s² + 1)(s + 122/85)`) and only `μ = n_q/E*` changes
  the nonlinear terms: every point of the path is a Hopf point (`Bautin.bpath_isHopf`). The
  physical range (`n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`) is `0 < μ < 22/5`.
* The chart: the critical chart `critι qC`, `critπ pC` of `qC = hopfQ 1 1 (6/5) (−1)` and its
  normalised left partner `pC` (rational at `ω = 1`), the reduced linear part `rotL 1`, and the
  stable eigenvector `w = (−85/122, 1, −1445/488)` (`A w = −(122/85) w`). The approximate centre
  manifold is `Bautin.manifold μ = H ∘ π`, `H(y) = h(y) w`, `h` a polynomial in `y` of degrees two
  to four whose coefficients are polynomials in `μ` (of degrees 2, 4, 6).
* Level: exact for every `μ > 0`. The trigonometric nonlinearities enter through the sixth-order
  Taylor remainders of `cos` and `sin`; every polynomial identity (the homological equations of
  degrees two to four, the jet, the Lyapunov chain) holds identically in `μ` (`ring`). The Bautin
  point is a root of the quartic `𝔔(μ)`; its location and the sign of `l₂` there are kernel-checked
  (a Möbius sign certificate, `decide +kernel`). No floating point, sampling or search.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3 (Bautin points, the
second Lyapunov coefficient); Carr, *Applications of Centre Manifold Theory* (1981), §2.4–2.5. The
generic laws are `theorem/Dynamics/CenterReductionBautin.lean`
(`unstable_of_dichotomy_reduced_l2_pos`, `localAsymptoticStable_of_dichotomy_reduced_l2_neg`),
`theorem/Dynamics/HopfDichotomy.lean` (`IsCritical.exists_dichotomy`),
`theorem/Dynamics/CenterManifoldChart.lean` and `theorem/Dynamics/PolySign.lean`
(`zeval_pos_of_zmob_Ico`); the Hopf data and the first-coefficient laws are those of
`QVDroopHopf` (`Model.hopf_data`, `mem_den_unstable_of_hopfNum_pos`,
`mem_den_locallyAsymptoticallyStable_of_hopfNum_neg`). The path, the centre manifold, the jet and
the Lyapunov chain were derived with SymPy in exact arithmetic over `ℚ(μ)` (untrusted, discovery
evidence only: an exact search found no rational Bautin point; on this path the Bautin points are
the roots of an irreducible quartic); every identity is checked here. Method: the four-state
template `theorem/GridTiedConverter/GFM/HopfBautinPoint.lean`.

Results.
* The path: `QVDroop.Bautin.bpath`, `Bautin.bpath_emf`, `Bautin.bpath_zsq`, `Bautin.bpath_data`,
  `Bautin.bpath_balance`, `Bautin.bpath_jacobian`, **`Bautin.bpath_isHopf`**,
  `Bautin.bpath_hopfFreq` (`ω = 1`), `Bautin.fderiv_field_zero`, `Bautin.A_apply`, `Bautin.fnl`,
  `Bautin.fnl_apply`.
* The critical chart: `Bautin.qC`, `Bautin.pC`, `Bautin.critι_C`, `Bautin.pC_apply`,
  `Bautin.critπ_C`, `Bautin.isCriticalPair_C`, `Bautin.isCritical_C`, `Bautin.wsv`,
  `Bautin.critπ_wsv`, `Bautin.A_wsv`, `Bautin.sub_critP` (`(1 − P) v = (v₁ − (ι π v)₁) w`).
* The manifold: `Bautin.hL2` … `Bautin.hL4`, `Bautin.hL`, `Bautin.manifoldH`, `Bautin.manifold`,
  `Bautin.critπ_manifoldH`, `Bautin.hasFDerivAt_manifoldH`, `Bautin.contDiffAt_manifold`,
  `Bautin.manifold_zero`, `Bautin.fderiv_manifold_zero`, `Bautin.critP_manifold`.
* The chart field and its quintic jet: `Bautin.chartPt`, `Bautin.chartField_eq`,
  `Bautin.chartPt_apply`, `Bautin.G0`, `Bautin.G1`, `Bautin.F1v`, `Bautin.F2v`,
  `Bautin.fnl_chartPt`, `Bautin.G_eq`; the truncations `Bautin.low2_eq`, `Bautin.low3_eq`,
  `Bautin.lowC_eq`, `Bautin.lowS_eq`, `Bautin.lowQ_eq`, the splits `Bautin.split2_isBigO`,
  `Bautin.split3_isBigO`, `Bautin.splitC_isBigO`, `Bautin.splitS_isBigO`,
  `Bautin.splitQ_isBigO`, the remainders `Bautin.f2_sub_low`, `Bautin.f3_sub_low`,
  `Bautin.fC_sub_low`, `Bautin.fS_sub_low`, `Bautin.fQ_sub_low`, `Bautin.F1_sub_low`,
  `Bautin.F2_sub_low`; `Bautin.cF`, `Bautin.cG`, `Bautin.cF_eq`, `Bautin.cG_eq`,
  `Bautin.G0_sub_jet`, `Bautin.G1_sub_jet`, `Bautin.jet_tail_bounds`.
* **The invariance defect is `O(‖u‖⁵)`** for every `μ > 0`: `Bautin.F1low4`,
  `Bautin.F1_sub_low4`, `Bautin.dcomp`, `Bautin.main_eq_high`, `Bautin.defect_eq`,
  `Bautin.dcomp_isBigO`, `Bautin.isOrder_defect`.
* The jet `Bautin.jet` (`Bautin.jetF_eq`, `Bautin.jetG_eq`), the Lyapunov chain `Bautin.jv_c30` …
  `Bautin.jv_l2` (polynomials in `μ`), **`Bautin.jet_l1`** (`l₁(J) = −𝔔(μ)/96802045600`,
  `Bautin.bautinQuartic`), `Bautin.jet_l2`, `Bautin.l2Num`, **`Bautin.l2Num_pos`** (`l₂ > 0` on
  `[11/100, 12/100)`), `Bautin.bautinQuartic_root_mem` (every positive root lies in
  `(11/100, 12/100)`: `𝔔` increases on `μ ≥ 0`), `Bautin.exists_bautinQuartic_root`,
  `Bautin.jet_l1_eq_zero`, `Bautin.jet_l2_pos`, `Bautin.bpath_hopfNumAt`
  (`hopfNum = −𝔔(μ)/5538336400`).

Family and connection conclusions.
No new family: connection conclusions on `QVDroop.family`.
* `QVDroop.mem_den_unstable_of_secondLyapunov_pos`,
  `QVDroop.mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`: a Hopf point with `l₁(J) = 0`
  is unstable for `l₂(J) > 0`, locally asymptotically stable for `l₂(J) < 0`, for an approximate
  centre manifold with invariance defect `O(‖u‖⁵)` and the quintic jet of its chart field in any
  chart of the critical plane.
* **`QVDroop.bautinPath_mem_den_unstable_of_bautinQuartic_eq_zero`**: the Bautin point of the path
  (the unique positive root `μ* ∈ (11/100, 12/100)` of `𝔔`, where `ℓ₁ = 0`) is unstable, a weak
  focus of the second order with `l₂ > 0`.
* `QVDroop.bautinPath_mem_den_unstable_of_bautinQuartic_neg` (`0 < μ < μ*`: subcritical) and
  `QVDroop.bautinPath_mem_den_locallyAsymptoticallyStable_of_bautinQuartic_pos` (`μ > μ*`:
  supercritical): every point of the path is decided; it is unstable iff `𝔔(μ) ≤ 0`.
* Not decided here: Bautin points off this path (the general Bautin set `hopfNum = 0` of the Hopf
  surface) and those of the virtual-impedance model.
-/

noncomputable section
namespace powerlib.GFM.QVDroop

open Complex Matrix Polynomial Filter Topology Asymptotics
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.Dynamics.LyapunovPerron (expFlow)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold
open powerlib.Dynamics.Degenerate
open powerlib.Dynamics.Degenerate.PlanarFocus (frameX frameY Jet5)
open powerlib.Criteria (droopJacobian)
open powerlib.Dynamics.PolyCertificate (zeval zeval_pos_of_zmob_Ico)

section Degenerate

/-- **A degenerate Hopf point with `l₂ > 0` is unstable**: a Hopf point (`A > 0`, `C > 0`,
`G = 0`; `M, D, ω_q > 0`, `E* ≠ 0`) with a critical pair `(q, p)` at its frequency `ω`, a chart
`ι`, `π` of the critical plane with linear part `L₂` (`L₂² = −ω²`), an approximate centre
manifold `φ` of its field (`C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`, values in `ker critP`,
invariance defect `O(‖u‖⁵)` for `A = DF(0)`, `f = F − A`) and the quintic jet `J` of the chart
field of `φ` in the rotation coordinates of `L₂`, with `l₁(J) = 0` and `l₂(J) > 0`
(`Dynamics.CenterManifold.unstable_of_dichotomy_reduced_l2_pos` with the dichotomy of
`Dynamics.CenterManifold.IsCritical.exists_dichotomy` and the factorization of
`Model.hopf_data`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_secondLyapunov_pos (m : Model)
    (hpar : 0 < m.q.M ∧ 0 < m.q.D ∧ 0 < m.q.ωq ∧ m.q.emf m.Qf ≠ 0)
    (h : m.IsHopf) {ω : ℝ} (hw : m.hopfFreq = ω) {q p : Fin 3 → ℂ}
    (hcp : IsCriticalPair m.field 0 ω q p)
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
  obtain ⟨hM, hD, hω, hE⟩ := hpar
  obtain ⟨hφ, hφ0, hDφ, hφP⟩ := hφ
  obtain ⟨hx, hy⟩ := hxy
  obtain ⟨hl1, hl2⟩ := hl
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  subst hw
  obtain ⟨-, -, hchar⟩ := m.hopf_data hM hD hω hE h
  have hcr := IsCriticalPair.isCritical hcp rfl
  obtain ⟨K, β, hβ, hcen, hst⟩ := hcr.exists_dichotomy hchar
    (re_neg_of_eval_X_add_C (div_pos h.2.1 hM))
  have hF : ContDiff ℝ 1 m.field := m.contDiff_field
  have hf0 : (fun x => m.field x - fderiv ℝ m.field 0 x) 0 = 0 := by simp [hcp.equilibrium]
  have hDf : fderiv ℝ (fun x => m.field x - fderiv ℝ m.field 0 x) 0 = 0 := by
    have hd := ((hF.differentiable one_ne_zero 0).hasFDerivAt.sub
      (fderiv ℝ m.field 0).hasFDerivAt).fderiv
    rw [show (fun x => m.field x - fderiv ℝ m.field 0 x) = m.field - ⇑(fderiv ℝ m.field 0)
      from rfl, hd, sub_self]
  have hFf : fullField (fderiv ℝ m.field 0) (fun x => m.field x - fderiv ℝ m.field 0 x) =
      m.field := by funext x; simp [fullField]
  rw [← hFf]
  exact unstable_of_dichotomy_reduced_l2_pos hcr.isCommutingProjection le_rfl (by linarith) hcen
    hst (hF.sub (fderiv ℝ m.field 0).contDiff) hf0 hDf hφ hφ0 hDφ hφP hdef hc hcp.freq_pos hrot
    hx hy hl1 hl2

/-- **A degenerate Hopf point with `l₂ < 0` is locally asymptotically stable** (hypotheses as
`mem_den_unstable_of_secondLyapunov_pos`, `l₂(J) < 0`;
`Dynamics.CenterManifold.localAsymptoticStable_of_dichotomy_reduced_l2_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg
    (m : Model) (hpar : 0 < m.q.M ∧ 0 < m.q.D ∧ 0 < m.q.ωq ∧ m.q.emf m.Qf ≠ 0)
    (h : m.IsHopf) {ω : ℝ} (hw : m.hopfFreq = ω) {q p : Fin 3 → ℂ}
    (hcp : IsCriticalPair m.field 0 ω q p)
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
  obtain ⟨hM, hD, hω, hE⟩ := hpar
  obtain ⟨hφ, hφ0, hDφ, hφP⟩ := hφ
  obtain ⟨hx, hy⟩ := hxy
  obtain ⟨hl1, hl2⟩ := hl
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  subst hw
  obtain ⟨-, -, hchar⟩ := m.hopf_data hM hD hω hE h
  have hcr := IsCriticalPair.isCritical hcp rfl
  obtain ⟨K, β, hβ, hcen, hst⟩ := hcr.exists_dichotomy hchar
    (re_neg_of_eval_X_add_C (div_pos h.2.1 hM))
  have hF : ContDiff ℝ 1 m.field := m.contDiff_field
  have hf0 : (fun x => m.field x - fderiv ℝ m.field 0 x) 0 = 0 := by simp [hcp.equilibrium]
  have hDf : fderiv ℝ (fun x => m.field x - fderiv ℝ m.field 0 x) 0 = 0 := by
    have hd := ((hF.differentiable one_ne_zero 0).hasFDerivAt.sub
      (fderiv ℝ m.field 0).hasFDerivAt).fderiv
    rw [show (fun x => m.field x - fderiv ℝ m.field 0 x) = m.field - ⇑(fderiv ℝ m.field 0)
      from rfl, hd, sub_self]
  have hFf : fullField (fderiv ℝ m.field 0) (fun x => m.field x - fderiv ℝ m.field 0 x) =
      m.field := by funext x; simp [fullField]
  rw [← hFf]
  exact localAsymptoticStable_of_dichotomy_reduced_l2_neg hcr.isCommutingProjection le_rfl
    (by linarith) hcen hst (hF.sub (fderiv ℝ m.field 0).contDiff) hf0 hDf hφ hφ0 hDφ hφP hdef hc
    hcp.freq_pos hrot hx hy hl1 hl2

end Degenerate

namespace Bautin

/-- **The path of Hopf points**, parametrised by `μ = n_q/E*` (`δ* = 0`, `E* = 1`). -/
def bpath (μ : ℝ) : Model :=
  ⟨⟨85 / 122, 10 / 61, 1, μ, 1, (2 - 5 * μ) / (20 * μ), (2 - 5 * μ) / (10 * μ),
    10 * μ / (2 + 5 * μ), 8 * μ / (2 + 5 * μ), 4 * μ / (2 + 5 * μ)⟩, 0, (2 - 5 * μ) / (20 * μ)⟩

variable {μ : ℝ}

/-- The EMF at the point, `E* = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_emf (μ : ℝ) : (bpath μ).q.emf (bpath μ).Qf = 1 := by
  simp [bpath, emf]

/-- `|Z|² = 80μ²/(2 + 5μ)²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_zsq (hμ : 0 < μ) :
    (bpath μ).q.zsq = 80 * μ ^ 2 / (2 + 5 * μ) ^ 2 := by
  have h : (2 + 5 * μ) ≠ 0 := by positivity
  simp only [zsq, bpath]; field_simp; ring

/-- **The Jacobian data are fixed along the path**: `P_δ = 1/2`, `n_q P_E = 2/5`, `Q_δ = −1`,
`K = 6/5`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_data (hμ : 0 < μ) :
    (bpath μ).q.Pδ 0 1 = 1 / 2 ∧ (bpath μ).q.nq * (bpath μ).q.PE 0 1 = 2 / 5 ∧
      (bpath μ).q.Qδ 0 1 = -1 ∧ (bpath μ).q.gain 0 1 = 6 / 5 := by
  have h : (2 + 5 * μ) ≠ 0 := by positivity
  have hμ0 : μ ≠ 0 := hμ.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Pδ, PE, Qδ, QE, gain, bpath_zsq hμ, Real.sin_zero, Real.cos_zero] <;>
    simp only [bpath] <;> field_simp <;> ring


/-- The selected point is balanced (`P = P_ref`, `Q = Q_f*`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_balance (hμ : 0 < μ) :
    (bpath μ).q.P 0 1 = (bpath μ).q.Pref ∧ (bpath μ).q.Q 0 1 = (bpath μ).Qf := by
  have h : (2 + 5 * μ) ≠ 0 := by positivity
  have hμ0 : μ ≠ 0 := hμ.ne'
  refine ⟨?_, ?_⟩ <;> simp only [P_eq, Q_eq, bpath_zsq hμ, Real.sin_zero, Real.cos_zero] <;>
    simp only [bpath] <;> field_simp <;> ring

/-- The Jacobian along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_jacobian (hμ : 0 < μ) :
    (bpath μ).jacobian = !![0, 1, 0; -61 / 85, -4 / 17, 244 / 425; -1, 0, -6 / 5] := by
  obtain ⟨h1, h2, h3, h4⟩ := bpath_data hμ
  rw [Model.jacobian, bpath_emf, jacobian_eq_droopJacobian, show (bpath μ).δ = 0 from rfl, h1,
    h2, h3, h4]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [droopJacobian, bpath]

/-- **Every point of the path is a Hopf point** (`A = C = 1`, `G = 0`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bpath_isHopf (hμ : 0 < μ) : (bpath μ).IsHopf := by
  obtain ⟨h1, h2, h3, h4⟩ := bpath_data hμ
  obtain ⟨hP, hQ⟩ := bpath_balance hμ
  have hM : (bpath μ).q.M ≠ 0 := by norm_num [bpath]
  have hω : (bpath μ).q.ωq ≠ 0 := by norm_num [bpath]
  have hcp : (bpath μ).q.coupling 0 1 = -2 / 5 := by
    rw [coupling, mul_assoc, ← mul_assoc, h2, h3]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Model.point, (bpath μ).q.field_eq_zero_iff hM hω]
    refine ⟨mk3_one _ _ _, ?_, ?_⟩ <;> simp only [mk3_zero, mk3_two]
    · rw [show (bpath μ).δ = 0 from rfl, bpath_emf]; exact hP
    · rw [show (bpath μ).δ = 0 from rfl, bpath_emf]; exact hQ
  · rw [bpath_emf, show (bpath μ).δ = 0 from rfl, routhTrace, h4]; norm_num [bpath]
  · rw [bpath_emf, show (bpath μ).δ = 0 from rfl, routhFold, h4, h1, hcp]; norm_num
  · rw [bpath_emf, show (bpath μ).δ = 0 from rfl, routhHopf, h4, h1, hcp]; norm_num [bpath]

/-- The Hopf frequency along the path, `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_hopfFreq (hμ : 0 < μ) : (bpath μ).hopfFreq = 1 := by
  obtain ⟨h1, -, -, h4⟩ := bpath_data hμ
  rw [Model.hopfFreq, bpath_emf, show (bpath μ).δ = 0 from rfl, h1, h4]
  norm_num [bpath]

/-- The linear part along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fderiv_field_zero (hμ : 0 < μ) :
    fderiv ℝ (bpath μ).field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
      !![0, 1, 0; -61 / 85, -4 / 17, 244 / 425; -1, 0, -6 / 5] := by
  rw [Model.fderiv_field, bpath_jacobian hμ]

/-- The linear part, componentwise. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_apply (hμ : 0 < μ) (x : State 3) (i : Fin 3) :
    fderiv ℝ (bpath μ).field 0 x i =
      ![x 1, -61 / 85 * x 0 - 4 / 17 * x 1 + 244 / 425 * x 2, -x 0 - 6 / 5 * x 2] i := by
  rw [fderiv_field_zero hμ, Dynamics.toEuclideanCLM_apply]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-- The nonlinear part `f = F − DF(0)` along the path. -/
def fnl (μ : ℝ) (x : State 3) : State 3 := (bpath μ).field x - fderiv ℝ (bpath μ).field 0 x

/-- **The nonlinearities** of the translated field along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fnl_apply (hμ : 0 < μ) (x : State 3) (i : Fin 3) :
    fnl μ x i = ![0, -(122 / 85) * ((2 * μ + 5 * μ ^ 2) / 10 * (x 2 * x 2) -
      (Real.cos (x 0) - 1) + 1 / 2 * (Real.sin (x 0) - x 0) + μ * ((Real.cos (x 0) - 1) * x 2) -
      μ / 2 * (Real.sin (x 0) * x 2)), (2 * μ + 5 * μ ^ 2) / 20 * (x 2 * x 2) -
      1 / 2 * (Real.cos (x 0) - 1) - (Real.sin (x 0) - x 0) +
      μ / 2 * ((Real.cos (x 0) - 1) * x 2) + μ * (Real.sin (x 0) * x 2)] i := by
  have h : (2 + 5 * μ) ≠ 0 := by positivity
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hf : (bpath μ).field x = (bpath μ).q.field (x + (bpath μ).point) := rfl
  rw [fnl, PiLp.sub_apply, hf, A_apply hμ]
  fin_cases i
  · simp [Model.point]
  · simp only [Fin.mk_one, field_apply_one, P_eq, bpath_zsq hμ, emf, Model.point]
    simp [bpath]
    field_simp
    ring
  · simp only [Fin.reduceFinMk, field_apply_two, Q_eq, bpath_zsq hμ, emf, Model.point]
    simp [bpath]
    field_simp
    ring


/-- The critical right eigenvector on the path, `hopfQ` at `ω = 1`, `K = 6/5`, `Q_δ = −1`. -/
abbrev qC : Fin 3 → ℂ := hopfQ 1 1 (6 / 5) (-1)

/-- The critical left eigenvector on the path. -/
abbrev pC : Fin 3 → ℂ := hopfP (85 / 122) (10 / 61) 1 1 (6 / 5) (-1)

/-- The critical chart `ι = critι qC`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critι_C (y : State 2) (i : Fin 3) :
    critι qC y i = ![11 / 5 * y 0 + 1 / 5 * y 1, 1 / 5 * y 0 - 11 / 5 * y 1, -y 0 - y 1] i := by
  rw [critι_apply]
  fin_cases i <;> simp [hopfQ, reV_apply, imV_apply] <;> ring

/-- The critical left vector `pC`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem pC_apply :
    pC 0 = 4335 / 22109 + 9665 / 44218 * I ∧ pC 1 = -7225 / 44218 + 5185 / 22109 * I ∧
      pC 2 = -2240 / 22109 + 614 / 22109 * I := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp only [pC, hopfP, hopfY, hopfN0, hopfB, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Complex.div_re, Complex.div_im,
      Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply] <;> norm_num

/-- The critical coordinates `π = critπ pC`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_C (x : State 3) :
    critπ pC x 0 = 18335 / 44218 * x 0 + 3145 / 44218 * x 1 - 1626 / 22109 * x 2 ∧
      critπ pC x 1 = -995 / 44218 * x 0 - 17595 / 44218 * x 1 - 2854 / 22109 * x 2 := by
  obtain ⟨p0, p1, p2⟩ := pC_apply
  rw [critπ_apply0, critπ_apply1]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, reV_apply, imV_apply, RCLike.inner_apply,
    conj_trivial, p0, p1, p2]
  simp
  constructor <;> ring

/-- The critical pair on the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCriticalPair_C (hμ : 0 < μ) :
    IsCriticalPair (bpath μ).field 0 1 qC pC := by
  have hM : 0 < (bpath μ).q.M := by norm_num [bpath]
  have hD : 0 < (bpath μ).q.D := by norm_num [bpath]
  have hω : 0 < (bpath μ).q.ωq := by norm_num [bpath]
  have hE : (bpath μ).q.emf (bpath μ).Qf ≠ 0 := by rw [bpath_emf]; norm_num
  obtain ⟨h1, -, h3, h4⟩ := bpath_data hμ
  have h := ((bpath μ).hopf_data hM hD hω hE (bpath_isHopf hμ)).1
  rw [bpath_hopfFreq hμ, bpath_emf, show (bpath μ).δ = 0 from rfl, h3, h4,
    show (bpath μ).q.ωq = 1 from rfl, show (bpath μ).q.M = 85 / 122 from rfl,
    show (bpath μ).q.D = 10 / 61 from rfl] at h
  exact h

/-- The critical data of the path at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCritical_C (hμ : 0 < μ) :
    IsCritical (fderiv ℝ (bpath μ).field 0) 1 qC pC :=
  IsCriticalPair.isCritical (isCriticalPair_C hμ) rfl

/-- The stable eigenvector `w = (−85/122, 1, −1445/488)` (`A w = −(122/85) w`), spanning
`ker π`. -/
def wsv : State 3 := WithLp.toLp 2 ![-85 / 122, 1, -1445 / 488]

/-- `w ∈ ker π`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_wsv : critπ pC wsv = 0 := by
  obtain ⟨h0, h1⟩ := critπ_C wsv
  ext i; fin_cases i
  · rw [Fin.zero_eta, h0]; simp [wsv]; norm_num
  · rw [Fin.mk_one, h1]; simp [wsv]; norm_num

/-- `A w = −(122/85) w`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_wsv (hμ : 0 < μ) :
    fderiv ℝ (bpath μ).field 0 wsv = (-122 / 85 : ℝ) • wsv := by
  ext i; rw [A_apply hμ]; fin_cases i <;> simp [wsv] <;> norm_num

/-- **`(1 − P) v = (v₁ − (ι π v)₁) w`**: the stable component of a vector. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem sub_critP (v : State 3) :
    v - critι qC (critπ pC v) =
      (v 1 - (1 / 5 * critπ pC v 0 - 11 / 5 * critπ pC v 1)) • wsv := by
  obtain ⟨h0, h1⟩ := critπ_C v
  ext i
  fin_cases i <;> simp [critι_C, h0, h1, wsv] <;> ring

/-! ## The approximate centre manifold -/

/-- `h` of the manifold, degree 2. -/
def hL2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-1882182267 / 6050127850 + 64839767 / 605012785 * μ -
    13002577 / 242005114 * μ ^ 2), 2, 0, 0), ((-794533967 / 3025063925 + 124482334 / 605012785 * μ -
    8398297 / 121002557 * μ ^ 2), 1, 1, 0), ((-1131842617 / 6050127850 + 78049317 / 605012785 * μ -
    36407667 / 242005114 * μ ^ 2), 0, 2, 0)]

/-- `−(85/122) h`, the angle part of the manifold, degree 2. -/
def aL2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((524542599 / 2420051140 - 18070099 / 242005114 * μ +
    18118345 / 484010228 * μ ^ 2), 2, 0, 0), ((221427499 / 1210025570 - 17345899 / 121002557 * μ +
    11702545 / 242005114 * μ ^ 2), 1, 1, 0), ((315431549 / 2420051140 - 21751449 / 242005114 * μ +
    50731995 / 484010228 * μ ^ 2), 0, 2, 0)]

/-- `−(1445/488) h`, the `Q_f` part of the manifold, degree 2. -/
def cL2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((8917224183 / 9680204560 - 307191683 / 968020456 * μ +
    308011865 / 1936040912 * μ ^ 2), 2, 0, 0), ((3764267483 / 4840102280 - 294880283 / 484010228 * μ
    + 198943265 / 968020456 * μ ^ 2), 1, 1, 0), ((5362336333 / 9680204560 - 369774633 / 968020456 *
    μ + 862443915 / 1936040912 * μ ^ 2), 0, 2, 0)]

/-- `h` of the manifold, degree 3. -/
def hL3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-4467279132517455864 / 26722024409195389625 -
    2576694105620002307 / 10688809763678155850 * μ - 66771381863801143 / 4275523905471262340 * μ ^ 2
    - 7415160951135241 / 213776195273563117 * μ ^ 3 - 12418746773520565 / 855104781094252468 * μ ^
    4), 3, 0, 0), ((-3319251933781374842 / 26722024409195389625 - 4826555012041910421 /
    10688809763678155850 * μ + 892097746201799401 / 4275523905471262340 * μ ^ 2 - 10373964128351968
    / 213776195273563117 * μ ^ 3 + 66343853193691555 / 855104781094252468 * μ ^ 4), 2, 1, 0),
    ((-2070524181130173042 / 26722024409195389625 - 2580656326314433371 / 10688809763678155850 * μ +
    428584605656389281 / 4275523905471262340 * μ ^ 2 - 616503953824301 / 16444322713351009 * μ ^ 3 +
    18619877128060555 / 855104781094252468 * μ ^ 4), 1, 2, 0), ((-1532524615003192064 /
    26722024409195389625 - 838528454444072757 / 10688809763678155850 * μ + 731998581033934237 /
    4275523905471262340 * μ ^ 2 - 1047980486365322 / 16444322713351009 * μ ^ 3 + 133279020232880935
    / 855104781094252468 * μ ^ 4), 0, 3, 0)]

/-- `−(85/122) h`, the angle part of the manifold, degree 3. -/
def aL3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((622489715186858604 / 5344404881839077925 +
    718095078615410479 / 4275523905471262340 * μ + 18608417896469171 / 1710209562188504936 * μ ^ 2 +
    10332601325352385 / 427552390547126234 * μ ^ 3 + 17304811077856525 / 1710209562188504936 * μ ^
    4), 3, 0, 0), ((462518712084289937 / 5344404881839077925 + 1345105495159220937 /
    4275523905471262340 * μ - 248617404679189997 / 1710209562188504936 * μ ^ 2 + 7227761892704240 /
    213776195273563117 * μ ^ 3 - 92446352810881675 / 1710209562188504936 * μ ^ 4), 2, 1, 0),
    ((288515664583712637 / 5344404881839077925 + 719199304054842087 / 4275523905471262340 * μ -
    119441611412436357 / 1710209562188504936 * μ ^ 2 + 859062886476485 / 32888645426702018 * μ ^ 3 -
    25945730424346675 / 1710209562188504936 * μ ^ 4), 1, 2, 0), ((213548511926674304 /
    5344404881839077925 + 233688257795889129 / 4275523905471262340 * μ - 203999604550440689 /
    1710209562188504936 * μ ^ 2 + 730150338861085 / 16444322713351009 * μ ^ 3 - 185716667537620975 /
    1710209562188504936 * μ ^ 4), 0, 3, 0)]

/-- `−(1445/488) h`, the `Q_f` part of the manifold, degree 3. -/
def cL3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((2645581289544149067 / 5344404881839077925 +
    12207616336461978143 / 17102095621885049360 * μ + 316343104239975907 / 6840838248754019744 * μ ^
    2 + 175654222530990545 / 1710209562188504936 * μ ^ 3 + 294181788323560925 / 6840838248754019744
    * μ ^ 4), 3, 0, 0), ((7862818105432928929 / 21377619527356311700 + 22866793417706755929 /
    17102095621885049360 * μ - 4226495879546229949 / 6840838248754019744 * μ ^ 2 + 30717988043993020
    / 213776195273563117 * μ ^ 3 - 1571587997784988475 / 6840838248754019744 * μ ^ 4), 2, 1, 0),
    ((4904766297923114829 / 21377619527356311700 + 12226388168932315479 / 17102095621885049360 * μ -
    2030507394011418069 / 6840838248754019744 * μ ^ 2 + 14604069070100245 / 131554581706808072 * μ ^
    3 - 441077417213893475 / 6840838248754019744 * μ ^ 4), 1, 2, 0), ((907581175688365792 /
    5344404881839077925 + 3972700382530115193 / 17102095621885049360 * μ - 3467993277357491713 /
    6840838248754019744 * μ ^ 2 + 12412555760638445 / 65777290853404036 * μ ^ 3 -
    3157183348139556575 / 6840838248754019744 * μ ^ 4), 0, 3, 0)]

/-- `h` of the manifold, degree 4. -/
def hL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-434129692694426974968816756093174409 /
    34636808857608652376076214993049077500 + 9455605689088020255918418734423262349 /
    73891858896231791735629258651838032000 * μ - 2418928635053926485972101778068070899 /
    29556743558492716694251703460735212800 * μ ^ 2 + 11216233834417111354652116106190389 /
    369459294481158958678146293259190160 * μ ^ 3 - 6573550296060814284387356659942087 /
    45471913166911871837310313016515712 * μ ^ 4 - 14911762849801573766879994987811725 /
    591134871169854333885034069214704256 * μ ^ 5 - 47427034380956333732932859593714875 /
    1182269742339708667770068138429408512 * μ ^ 6), 4, 0, 0),
    ((-6219808486499946036636029408614544147 / 69273617715217304752152429986098155000 +
    8103550223689749734058794159662819697 / 55418894172173843801721943988878524000 * μ +
    16304874979776087698101544249899903 / 540672138265110671236311648671985600 * μ ^ 2 +
    9499341801204113947631930357822939 / 92364823620289739669536573314797540 * μ ^ 3 +
    377617628789813026886956589646773 / 11367978291727967959327578254128928 * μ ^ 4 +
    306225569253748974146790873982325 / 147783717792463583471258517303676064 * μ ^ 5 +
    11992383107940450801120770332741125 / 295567435584927166942517034607352128 * μ ^ 6), 3, 1, 0),
    ((-299067689071607193880858622910607 / 4219113083331342027660176014745000 +
    2293004664902218619210297004548439 / 6750580933330147244256281623592000 * μ +
    202994599807066685276737577860441 / 2700232373332058897702512649436800 * μ ^ 2 +
    25074647784792226710996911000983 / 67505809333301472442562816235920 * μ ^ 3 -
    26541385518191079174590760931931 / 54004647466641177954050252988736 * μ ^ 4 -
    2741186152092675306257299375 / 4154203651280090611850019460672 * μ ^ 5 -
    19371739660870897044591455270375 / 108009294933282355908100505977472 * μ ^ 6), 2, 2, 0),
    ((-1812210685884210642241548891234175747 / 69273617715217304752152429986098155000 +
    2505880609189274031986656578230384549 / 18472964724057947933907314662959508000 * μ +
    1036055520950372492169541864187025171 / 7389185889623179173562925865183803200 * μ ^ 2 +
    5389845416411491412796440835817807 / 46182411810144869834768286657398770 * μ ^ 3 -
    1095347298170548499506310190878357 / 11367978291727967959327578254128928 * μ ^ 4 -
    9106167371286477519384543454089325 / 147783717792463583471258517303676064 * μ ^ 5 +
    5972486911343458080720707539786875 / 295567435584927166942517034607352128 * μ ^ 6), 1, 3, 0),
    ((-1262779238995227770354121574531484743 / 69273617715217304752152429986098155000 +
    18464257151474805735293098475569808947 / 221675576688695375206887775955514096000 * μ +
    15840911084093585925402203265062614783 / 88670230675478150082755110382205638400 * μ ^ 2 +
    14425004353325376183415119985425057 / 184729647240579479339073146629595080 * μ ^ 3 -
    16331807395153690793702111773445847 / 45471913166911871837310313016515712 * μ ^ 4 +
    1073812963216739246534397885109975 / 591134871169854333885034069214704256 * μ ^ 5 -
    267413962110105766378708381157835875 / 1182269742339708667770068138429408512 * μ ^ 6), 0, 4, 0)]

/-- `−(85/122) h`, the angle part of the manifold, degree 4. -/
def aL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((120986963537791124171637456616130573 /
    13854723543043460950430485997219631000 - 2635168798598300727059231450576974753 /
    29556743558492716694251703460735212800 * μ + 674127652392077873139766069297659103 /
    11822697423397086677700681384294085120 * μ ^ 2 - 190675975185090893029085973805236613 /
    9014806785340278591746769555524239904 * μ ^ 3 + 558751775165169214172925316095077395 /
    5547573406363248364151858188014916864 * μ ^ 4 + 1267499842233133770184799573963996625 /
    72118454282722228733974156444193919232 * μ ^ 5 + 4031297922381288367299293065465764375 /
    144236908565444457467948312888387838464 * μ ^ 6), 4, 0, 0),
    ((1733389250336050534800204917154872959 / 27709447086086921900860971994439262000 -
    2258366455782389270147532798594556309 / 22167557668869537520688777595551409600 * μ -
    4543981551740876899470922168004891 / 216268855306044268494524659468794240 * μ ^ 2 -
    2647357551155244870651521575130983 / 36945929448115895867814629325919016 * μ ^ 3 -
    526188499133346021071988690491405 / 22735956583455935918655156508257856 * μ ^ 4 -
    426707760435551849220938103090125 / 295567435584927166942517034607352128 * μ ^ 5 -
    16710697773359644558938778332508125 / 591134871169854333885034069214704256 * μ ^ 6), 3, 1, 0),
    ((83346733019956103212698304745579 / 1687645233332536811064070405898000 -
    639034086939962566009427034054483 / 2700232373332058897702512649436800 * μ -
    56572265520002190978762931534877 / 1080092949332823559081005059774720 * μ ^ 2 -
    426269012341467854086947487016711 / 1647141747732555927598532716156448 * μ ^ 3 +
    2256017769046241729840214679214135 / 6588566990930223710394130864625792 * μ ^ 4 +
    233000822927877401031870446875 / 506812845456171054645702374201984 * μ ^ 5 +
    1646597871174026248790273697981875 / 13177133981860447420788261729251584 * μ ^ 6), 2, 2, 0),
    ((505042322295599687182071002475098159 / 27709447086086921900860971994439262000 -
    698360169774059976127428882457648153 / 7389185889623179173562925865183803200 * μ -
    288736784527152989621019863789826687 / 2955674355849271669425170346073521280 * μ ^ 2 -
    1502088066868776295369499905063979 / 18472964724057947933907314662959508 * μ ^ 3 +
    1526303612204862663246497806961645 / 22735956583455935918655156508257856 * μ ^ 4 +
    12688921746874599822093216288485125 / 295567435584927166942517034607352128 * μ ^ 5 -
    8322317827281867817397707227571875 / 591134871169854333885034069214704256 * μ ^ 6), 1, 3, 0),
    ((351922082998670034360984701098938371 / 27709447086086921900860971994439262000 -
    5145776583197896680327584821060438559 / 88670230675478150082755110382205638400 * μ -
    4414680138190015749702253368951876251 / 35468092270191260033102044152882255360 * μ ^ 2 -
    245225074006531395118057039752225969 / 4507403392670139295873384777762119952 * μ ^ 3 +
    1388203628588063717464679500742896995 / 5547573406363248364151858188014916864 * μ ^ 4 -
    91274101873422835955423820234347875 / 72118454282722228733974156444193919232 * μ ^ 5 +
    22730186779358990142190212398416049375 / 144236908565444457467948312888387838464 * μ ^ 6), 0, 4,
    0)]

/-- `−(1445/488) h`, the `Q_f` part of the manifold, degree 4. -/
def cL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((2056778380142449110917836762474219741 /
    55418894172173843801721943988878524000 - 44797869576171112360006934659808570801 /
    118226974233970866777006813842940851200 * μ + 11460170090665323843376023178060204751 /
    47290789693588346710802725537176340480 * μ ^ 2 - 3241491578146545181494461554689022421 /
    36059227141361114366987078222096959616 * μ ^ 3 + 9498780177807876640939730373616315715 /
    22190293625452993456607432752059667456 * μ ^ 4 + 21547497317963274093141592757387942625 /
    288473817130888914935896625776775676928 * μ ^ 5 + 68532064680481902244087982112917994375 /
    576947634261777829871793251553551353856 * μ ^ 6), 4, 0, 0),
    ((29467617255712859091603483591632840303 / 110837788344347687603443887977757048000 -
    38392229748300617592508057576107457253 / 88670230675478150082755110382205638400 * μ -
    77247686379594907291005676856083147 / 865075421224177073978098637875176960 * μ ^ 2 -
    45005078369639162801075866777226711 / 147783717792463583471258517303676064 * μ ^ 3 -
    8945204485266882358223807738353885 / 90943826333823743674620626033031424 * μ ^ 4 -
    7254031927404381436755947752532125 / 1182269742339708667770068138429408512 * μ ^ 5 -
    284081862147113957501959231652638125 / 2364539484679417335540136276858817024 * μ ^ 6), 3, 1, 0),
    ((1416894461339253754615871180674843 / 6750580933330147244256281623592000 -
    10863579477979363622160259578926211 / 10800929493328235590810050597747200 * μ -
    961728513840037246638969836092909 / 4320371797331294236324020239098880 * μ ^ 2 -
    7246573209804953519478107279284087 / 6588566990930223710394130864625792 * μ ^ 3 +
    38352302073786109407283649546640295 / 26354267963720894841576523458503168 * μ ^ 4 +
    3961013989773915817541797596875 / 2027251381824684218582809496807936 * μ ^ 5 +
    27992163809958446229434652865691875 / 52708535927441789683153046917006336 * μ ^ 6), 2, 2, 0),
    ((8585719479025194682095207042076668703 / 110837788344347687603443887977757048000 -
    11872122886159019594166291001780018601 / 29556743558492716694251703460735212800 * μ -
    4908525336961600823557337684427053679 / 11822697423397086677700681384294085120 * μ ^ 2 -
    25535497136769197021281498386087643 / 73891858896231791735629258651838032 * μ ^ 3 +
    25947161407482665275190462718347965 / 90943826333823743674620626033031424 * μ ^ 4 +
    215711669696868196975584676904247125 / 1182269742339708667770068138429408512 * μ ^ 5 -
    141479403063791752895761022868721875 / 2364539484679417335540136276858817024 * μ ^ 6), 1, 3, 0),
    ((5982675410977390584136739918681952307 / 110837788344347687603443887977757048000 -
    87478201914364243565568941958027455503 / 354680922701912600331020441528822553600 * μ -
    75049562349230267744938307272181896267 / 141872369080765040132408176611529021440 * μ ^ 2 -
    4168826258111033717006969675787841473 / 18029613570680557183493539111048479808 * μ ^ 3 +
    23599461685997083196899551512629248915 / 22190293625452993456607432752059667456 * μ ^ 4 -
    1551659731848188211242204943983913875 / 288473817130888914935896625776775676928 * μ ^ 5 +
    386413175249102832417233610773072839375 / 576947634261777829871793251553551353856 * μ ^ 6), 0,
    4, 0)]

/-- The weight-five truncation of `cos x₀ − 1`, degrees two to four. -/
def low2L4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-121 / 50), 2, 0, 0), ((-11 / 25), 1, 1, 0), ((-1 /
    50), 0, 2, 0), ((-5769968589 / 12100255700 + 198771089 / 1210025570 * μ - 39860359 / 484010228 *
    μ ^ 2), 3, 0, 0), ((-5395947577 / 12100255700 + 399679877 / 1210025570 * μ - 55114867 /
    484010228 * μ ^ 2), 2, 1, 0), ((-3912602037 / 12100255700 + 273957737 / 1210025570 * μ -
    116291407 / 484010228 * μ ^ 2), 1, 2, 0), ((-315431549 / 12100255700 + 21751449 / 1210025570 * μ
    - 10146399 / 484010228 * μ ^ 2), 0, 3, 0), ((48882360184284798078509389 /
    70199827003932656360460000 - 82675854092503803256429 / 233999423346442187868200 * μ -
    3260933458909933726911 / 93599769338576875147280 * μ ^ 2 - 471480648469055127429 /
    9359976933857687514728 * μ ^ 3 - 859673314126555048385 / 37439907735430750058912 * μ ^ 4), 4, 0,
    0), ((1782740397573170520597449 / 17549956750983164090115000 - 19918882256736821024297 /
    29249927918305273483525 * μ + 6776812928851563503419 / 23399942334644218786820 * μ ^ 2 -
    82178680669965292207 / 1169997116732210939341 * μ ^ 3 + 1077224544431877754015 /
    9359976933857687514728 * μ ^ 4), 3, 1, 0), ((-1552226888639890468884341 /
    11699971167322109393410000 - 44172530248040110024977 / 116999711673221093934100 * μ +
    6050775060060017756247 / 46799884669288437573640 * μ ^ 2 - 215765183949907897947 /
    4679988466928843757364 * μ ^ 3 + 731850136696701424495 / 18719953867715375029456 * μ ^ 4), 2, 2,
    0), ((-2099351622743286083374981 / 17549956750983164090115000 - 3473616958287565528562 /
    29249927918305273483525 * μ + 5569737309753706636579 / 23399942334644218786820 * μ ^ 2 -
    97735996071362217567 / 1169997116732210939341 * μ ^ 3 + 2217098853426139864065 /
    9359976933857687514728 * μ ^ 4), 1, 3, 0), ((-1152623799483294544410971 /
    70199827003932656360460000 + 183363833162763646011 / 233999423346442187868200 * μ +
    576168272358968851909 / 93599769338576875147280 * μ ^ 2 + 5059987826882782631 /
    9359976933857687514728 * μ ^ 3 + 607477241726135559215 / 37439907735430750058912 * μ ^ 4), 0, 4,
    0)]

/-- The weight-five truncation of `cos x₀ − 1`, degree five. -/
def low2L5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((11783409655142708747161367163598295683 /
    34636808857608652376076214993049077500 + 15927624787274848937464496067257973713 /
    443351153377390750413775551911028192000 * μ - 9432490400624779964717737352429805103 /
    177340461350956300165510220764411276800 * μ ^ 2 + 1614563255158159167409699791698420903 /
    45074033926701392958733847777621199520 * μ ^ 3 - 1233669711597797931668951427362752429 /
    5547573406363248364151858188014916864 * μ ^ 4 - 2799254290797332082302773399839164975 /
    72118454282722228733974156444193919232 * μ ^ 5 - 8923488790818791531946506812935115625 /
    144236908565444457467948312888387838464 * μ ^ 6), 5, 0, 0),
    ((6933404415009361303569664458461821391 / 27709447086086921900860971994439262000 -
    3675262696877404908231723390994784383 / 29556743558492716694251703460735212800 * μ +
    489385144072149629877504129935656741 / 2364539484679417335540136276858817024 * μ ^ 2 +
    1090132585302468483682197064535920877 / 9014806785340278591746769555524239904 * μ ^ 3 +
    285927454884890359504132432113681525 / 5547573406363248364151858188014916864 * μ ^ 4 -
    386477205266680381882534096565210225 / 72118454282722228733974156444193919232 * μ ^ 5 +
    8385332381189912342316523919952258625 / 144236908565444457467948312888387838464 * μ ^ 6), 4, 1,
    0), ((152898000681046496028659832970663159 / 923648236202897396695365733147975400 +
    9746349440976325728585622855372272169 / 44335115337739075041377555191102819200 * μ +
    7539807517974294666342551248007840983 / 17734046135095630016551022076441127680 * μ ^ 2 +
    4547850037952542075912034000653015637 / 9014806785340278591746769555524239904 * μ ^ 3 -
    1995318070937303027185552247838529155 / 2773786703181624182075929094007458432 * μ ^ 4 -
    499087341772127832440756185393079575 / 36059227141361114366987078222096959616 * μ ^ 5 -
    19265302488343395551778818454496395875 / 72118454282722228733974156444193919232 * μ ^ 6), 3, 2,
    0), ((-115952504059231361104936767150069061 / 13854723543043460950430485997219631000 +
    6216364581282740124970988119339352767 / 44335115337739075041377555191102819200 * μ +
    6724339324379786937820497197977065601 / 17734046135095630016551022076441127680 * μ ^ 2 +
    1232284909604123204341467133853786355 / 9014806785340278591746769555524239904 * μ ^ 3 -
    415055301041412311446822669884701685 / 2773786703181624182075929094007458432 * μ ^ 4 -
    4188290478630765602751990314150495425 / 36059227141361114366987078222096959616 * μ ^ 5 +
    1186031604024709270027901367487920875 / 72118454282722228733974156444193919232 * μ ^ 6), 2, 3,
    0), ((-553573949138906507316881691377917111 / 13854723543043460950430485997219631000 +
    715754955171572232874558548094171283 / 5911348711698543338850340692147042560 * μ +
    4071037893260123229909021862806051523 / 11822697423397086677700681384294085120 * μ ^ 2 +
    364074457525266309084085719768050827 / 4507403392670139295873384777762119952 * μ ^ 3 -
    2886377259514934199456307967097486065 / 5547573406363248364151858188014916864 * μ ^ 4 -
    1991714144276928247715630518088282775 / 72118454282722228733974156444193919232 * μ ^ 5 -
    48613505672492551967823406797473891125 / 144236908565444457467948312888387838464 * μ ^ 6), 1, 4,
    0), ((-349803191152025088801283506211110291 / 46182411810144869834768286657398770000 +
    3526421543605732935902513827861054703 / 443351153377390750413775551911028192000 * μ +
    7325135037931935567935534390772590987 / 177340461350956300165510220764411276800 * μ ^ 2 -
    255941095326730014856108942989595651 / 22537016963350696479366923888810599760 * μ ^ 3 -
    107620365059524759623835429796499959 / 5547573406363248364151858188014916864 * μ ^ 4 -
    1021283444513738197900282997512030825 / 72118454282722228733974156444193919232 * μ ^ 5 -
    2904293652850227689415221280378023875 / 144236908565444457467948312888387838464 * μ ^ 6), 0, 5,
    0)]

/-- The weight-five truncation of `sin x₀ − x₀`, degrees two to four. -/
def low3L4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-1331 / 750), 3, 0, 0), ((-121 / 250), 2, 1, 0),
    ((-11 / 250), 1, 2, 0), ((-1 / 750), 0, 3, 0), ((-63469654479 / 121002557000 + 2186481979 /
    12100255700 * μ - 438463949 / 4840102280 * μ ^ 2), 4, 0, 0), ((-8140673992 / 15125319625 +
    1148812434 / 3025063925 * μ - 80765487 / 605012785 * μ ^ 2), 3, 1, 0), ((-6054321248 /
    15125319625 + 853303746 / 3025063925 * μ - 166790043 / 605012785 * μ ^ 2), 2, 2, 0),
    ((-1845587269 / 30250639250 + 128305919 / 3025063925 * μ - 56975449 / 1210025570 * μ ^ 2), 1, 3,
    0), ((-315431549 / 121002557000 + 21751449 / 12100255700 * μ - 10146399 / 4840102280 * μ ^ 2),
    0, 4, 0)]

/-- The weight-five truncation of `sin x₀ − x₀`, degree five. -/
def low3L5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((168342397655041751132376539 /
    1754995675098316409011500000 - 54236017102602838510139 / 146249639591526367417625 * μ -
    11773579819588401238589 / 233999423346442187868200 * μ ^ 2 - 2449251303762772011437 /
    46799884669288437573640 * μ ^ 3 - 974495934716648296821 / 37439907735430750058912 * μ ^ 4), 5,
    0, 0), ((-55256710682155430840057351 / 350999135019663281802300000 - 85830128927380058048777 /
    116999711673221093934100 * μ + 2650335016457741962873 / 9359976933857687514728 * μ ^ 2 -
    675278343232176711997 / 9359976933857687514728 * μ ^ 3 + 4576647529905756303165 /
    37439907735430750058912 * μ ^ 4), 4, 1, 0), ((-42554884124374673152290091 /
    175499567509831640901150000 - 48898030417322345125161 / 116999711673221093934100 * μ +
    5129294302957950364003 / 46799884669288437573640 * μ ^ 2 - 172715172167397040087 /
    4679988466928843757364 * μ ^ 3 + 912219909640522962535 / 18719953867715375029456 * μ ^ 4), 3, 2,
    0), ((-31664820337884590384668181 / 175499567509831640901150000 - 14530960302140720848283 /
    116999711673221093934100 * μ + 10633255190949611986891 / 46799884669288437573640 * μ ^ 2 -
    343407474148949271307 / 4679988466928843757364 * μ ^ 3 + 4836897526420387995005 /
    18719953867715375029456 * μ ^ 4), 2, 3, 0), ((-14732211371599900125010621 /
    350999135019663281802300000 + 126034253155077061723 / 23399942334644218786820 * μ +
    85007997755071453393 / 11699971167322109393410 * μ ^ 2 + 42506218667644033243 /
    9359976933857687514728 * μ ^ 3 + 1309856850206630884075 / 37439907735430750058912 * μ ^ 4), 1,
    4, 0), ((-4379337744354561938133911 / 1754995675098316409011500000 + 365584917019916212257 /
    292499279183052734835250 * μ - 135080390836398259747 / 116999711673221093934100 * μ ^ 2 +
    46619560994584651963 / 46799884669288437573640 * μ ^ 3 + 40181262630555144149 /
    37439907735430750058912 * μ ^ 4), 0, 5, 0)]

/-- The weight-five truncation of `(cos x₀ − 1) x₂`, degrees two to four. -/
def lowCL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((121 / 50), 3, 0, 0), ((143 / 50), 2, 1, 0), ((23 /
    50), 1, 2, 0), ((1 / 50), 0, 3, 0), ((-848185382583 / 484010228000 + 29219350083 / 48401022800 *
    μ - 5859472773 / 19360409120 * μ ^ 2), 4, 0, 0), ((-3175456809 / 2326972250 + 520973143 /
    465394450 * μ - 69087473 / 186157780 * μ ^ 2), 3, 1, 0), ((-28190356573 / 30250639250 +
    3884893771 / 6050127850 * μ - 1978399361 / 2420051140 * μ ^ 2), 2, 2, 0), ((10905352287 /
    121002557000 - 775891237 / 12100255700 * μ + 295795427 / 4840102280 * μ ^ 2), 1, 3, 0),
    ((7254925627 / 484010228000 - 500283327 / 48401022800 * μ + 233367177 / 19360409120 * μ ^ 2), 0,
    4, 0)]

/-- The weight-five truncation of `(cos x₀ − 1) x₂`, degree five. -/
def lowCL5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-327628170847149827212404179 /
    140399654007865312720920000 - 5014393180713670838055909 / 4679988466928843757364000 * μ -
    525891915603660644865501 / 1871995386771537502945600 * μ ^ 2 - 6828830564701740301371 /
    46799884669288437573640 * μ ^ 3 - 3527204366427421033683 / 37439907735430750058912 * μ ^ 4), 5,
    0, 0), ((-25154522945951152289661367 / 9359976933857687514728000 - 1545738026877002653630513 /
    935997693385768751472800 * μ + 50712308994312598895637 / 74879815470861500117824 * μ ^ 2 -
    1866329834138749794957 / 18719953867715375029456 * μ ^ 3 + 15345555497952780688645 /
    37439907735430750058912 * μ ^ 4), 4, 1, 0), ((-22530015676715061454361593 /
    14039965400786531272092000 - 18864471053792286007493 / 116999711673221093934100 * μ -
    44602454691316203197537 / 93599769338576875147280 * μ ^ 2 + 319586722852488822487 /
    2339994233464421878682 * μ ^ 3 + 140848237415720677885 / 37439907735430750058912 * μ ^ 4), 3, 2,
    0), ((-2216894432897682263347511 / 2807993080157306254418400 + 20128589589842612806533 /
    58499855836610546967050 * μ + 4543253755797396303309 / 23399942334644218786820 * μ ^ 2 +
    133981064525244418623 / 9359976933857687514728 * μ ^ 3 + 28845148886099908229705 /
    37439907735430750058912 * μ ^ 4), 2, 3, 0), ((-1335301984039434718518129 /
    9359976933857687514728000 + 52464866069354953164949 / 187199538677153750294560 * μ -
    154034327760301873927427 / 374399077354307500589120 * μ ^ 2 + 1936076155860385443609 /
    9359976933857687514728 * μ ^ 3 - 187288941471387320625 / 1169997116732210939341 * μ ^ 4), 1, 4,
    0), ((-199034048995951748820989 / 140399654007865312720920000 + 67794861245040652398021 /
    4679988466928843757364000 * μ - 48874625807907092509021 / 1871995386771537502945600 * μ ^ 2 +
    1095189030564577146383 / 93599769338576875147280 * μ ^ 3 - 76440224831721587081 /
    4679988466928843757364 * μ ^ 4), 0, 5, 0)]

/-- The weight-five truncation of `sin x₀ · x₂`, degrees two to four. -/
def lowSL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-11 / 5), 2, 0, 0), ((-12 / 5), 1, 1, 0), ((-1 / 5),
    0, 2, 0), ((87598614033 / 48401022800 - 3017706533 / 4840102280 * μ + 605152723 / 1936040912 * μ
    ^ 2), 3, 0, 0), ((171931489 / 114966800 - 13632589 / 11496680 * μ + 1831019 / 4598672 * μ ^ 2),
    2, 1, 0), ((51348503689 / 48401022800 - 3528416589 / 4840102280 * μ + 1680405579 / 1936040912 *
    μ ^ 2), 1, 2, 0), ((-946294647 / 48401022800 + 65254347 / 4840102280 * μ - 30439197 / 1936040912
    * μ ^ 2), 0, 3, 0), ((82748689065268859736825739 / 28079930801573062544184000 +
    147987926490825338546231 / 116999711673221093934100 * μ + 17177093736981044185353 /
    93599769338576875147280 * μ ^ 2 + 3332803943931418829199 / 18719953867715375029456 * μ ^ 3 +
    6772522010941230384835 / 74879815470861500117824 * μ ^ 4), 4, 0, 0),
    ((23172735465151783807670419 / 7019982700393265636046000 + 519834101887590135469403 /
    233999423346442187868200 * μ - 22866263730231675392237 / 23399942334644218786820 * μ ^ 2 +
    1894313483910421910043 / 9359976933857687514728 * μ ^ 3 - 8189892409216747304565 /
    18719953867715375029456 * μ ^ 4), 3, 1, 0), ((6309768012848749309244549 /
    4679988466928843757364000 + 103673004450512784565131 / 116999711673221093934100 * μ -
    10032181775112632242337 / 93599769338576875147280 * μ ^ 2 + 69015982363016861129 /
    1169997116732210939341 * μ ^ 3 - 2818515865577251018395 / 37439907735430750058912 * μ ^ 4), 2,
    2, 0), ((4026792276270749954012129 / 7019982700393265636046000 + 31012665114450392700163 /
    233999423346442187868200 * μ - 30860423829944491285709 / 46799884669288437573640 * μ ^ 2 +
    1892333066702113127333 / 9359976933857687514728 * μ ^ 3 - 16125231318906943444865 /
    18719953867715375029456 * μ ^ 4), 1, 3, 0), ((1896571000510343554584659 /
    28079930801573062544184000 - 6304911381961540811727 / 58499855836610546967050 * μ +
    984851977842697483773 / 5849985583661054696705 * μ ^ 2 - 1623724000261976470011 /
    18719953867715375029456 * μ ^ 3 + 4716011247870009516735 / 74879815470861500117824 * μ ^ 4), 0,
    4, 0)]

/-- The weight-five truncation of `sin x₀ · x₂`, degree five. -/
def lowSL5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-113990068449217615742723165199787967431 /
    138547235430434609504304859972196310000 - 224281948649666682373092733081470916981 /
    1773404613509563001655102207644112768000 * μ + 166612333918995465156659712519751242251 /
    709361845403825200662040883057645107200 * μ ^ 2 - 15425223812063596834908996340062331811 /
    180296135706805571834935391110484798080 * μ ^ 3 + 18812446702487124209985240443997378433 /
    22190293625452993456607432752059667456 * μ ^ 4 + 42700152418657552712643593232422148875 /
    288473817130888914935896625776775676928 * μ ^ 5 + 136502884901253573679990498729511286125 /
    576947634261777829871793251553551353856 * μ ^ 6), 5, 0, 0), ((8629922369365665566486234052368231
    / 87757552133291914175331661106696000 + 405270311757940139150345666380410853 /
    842472500479602376083183946624281600 * μ - 66147590810883505981681274888654791 /
    67397800038368190086654715729942528 * μ ^ 2 - 21166172553834760692175899393632829 /
    85651370882092908235123701240135296 * μ ^ 3 - 20287294203000276108216981176011325 /
    52708535927441789683153046917006336 * μ ^ 4 + 19171394915338987279641023225792825 /
    685210967056743265880989609921082368 * μ ^ 5 - 347097674486244104703564415104891625 /
    1370421934113486531761979219842164736 * μ ^ 6), 4, 1, 0),
    ((3375837976653253855852430464208892617 / 11083778834434768760344388797775704800 -
    51977238064299164949306612904234620351 / 59113487116985433388503406921470425600 * μ -
    40828158972984957953703801498182644737 / 23645394846794173355401362768588170240 * μ ^ 2 -
    53261861887863582834261215773428213609 / 36059227141361114366987078222096959616 * μ ^ 3 +
    28994821285071322106055530086390787135 / 11095146812726496728303716376029833728 * μ ^ 4 +
    16667881478583046775333288035251502275 / 144236908565444457467948312888387838464 * μ ^ 5 +
    297016934387537085559642203440596997375 / 288473817130888914935896625776775676928 * μ ^ 6), 3,
    2, 0), ((30811610996798408985561064996549828447 / 55418894172173843801721943988878524000 -
    55402565712979904996252306009372982179 / 177340461350956300165510220764411276800 * μ -
    111185144428351265446012346469746973917 / 70936184540382520066204088305764510720 * μ ^ 2 +
    5713278959654988687091388544634043305 / 36059227141361114366987078222096959616 * μ ^ 3 -
    625571806802963235477645158945735455 / 11095146812726496728303716376029833728 * μ ^ 4 +
    78189994775258134648014731378093325725 / 144236908565444457467948312888387838464 * μ ^ 5 -
    64978254756927155090092149652574817375 / 288473817130888914935896625776775676928 * μ ^ 6), 2, 3,
    0), ((4867289923634063407387101281846623919 / 18472964724057947933907314662959508000 -
    22383210242100827733755700968021283293 / 70936184540382520066204088305764510720 * μ -
    197040989861099633617935840314622267373 / 141872369080765040132408176611529021440 * μ ^ 2 +
    485956721549607727947816002211947481 / 18029613570680557183493539111048479808 * μ ^ 3 +
    37909302797764824853718863110308644405 / 22190293625452993456607432752059667456 * μ ^ 4 +
    48585911616818488392114472442214874675 / 288473817130888914935896625776775676928 * μ ^ 5 +
    726856237268224715550414337989791631625 / 576947634261777829871793251553551353856 * μ ^ 6), 1,
    4, 0), ((24512800663141150929792839344917615461 / 554188941721738438017219439888785240000 +
    22134764334586892584440523557505230463 / 591134871169854333885034069214704256000 * μ -
    27934348958323949515133761131288049093 / 236453948467941733554013627685881702400 * μ ^ 2 +
    17775324979350482124475814532478612987 / 90148067853402785917467695555242399040 * μ ^ 3 -
    161307669256776333708005455912596077 / 541226673791536425770912993952674816 * μ ^ 4 +
    35399065467330427714679758185143222325 / 288473817130888914935896625776775676928 * μ ^ 5 -
    69457397970348785612090048215425953625 / 576947634261777829871793251553551353856 * μ ^ 6), 0, 5,
    0)]

/-- The weight-five truncation of `x₂²`, degrees two to four. -/
def lowQL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((1), 2, 0, 0), ((2), 1, 1, 0), ((1), 0, 2, 0),
    ((-8917224183 / 4840102280 + 307191683 / 484010228 * μ - 308011865 / 968020456 * μ ^ 2), 3, 0,
    0), ((-16445759149 / 4840102280 + 896952249 / 484010228 * μ - 705898395 / 968020456 * μ ^ 2), 2,
    1, 0), ((-12890871299 / 4840102280 + 959535199 / 484010228 * μ - 1260330445 / 968020456 * μ ^
    2), 1, 2, 0), ((-5362336333 / 4840102280 + 369774633 / 484010228 * μ - 862443915 / 968020456 * μ
    ^ 2), 0, 3, 0), ((-1059269461948083138441291 / 7487981547086150011782400 -
    753392765996270619764113 / 374399077354307500589120 * μ + 45126520897948031505345 /
    149759630941723000235648 * μ ^ 2 - 22942573313888691634215 / 74879815470861500117824 * μ ^ 3 -
    18179839410572575898875 / 299519261883446000471296 * μ ^ 4), 4, 0, 0),
    ((-548117828510259114648191 / 1871995386771537502945600 - 535186842460970049812763 /
    93599769338576875147280 * μ + 80718600556469585163195 / 37439907735430750058912 * μ ^ 2 -
    15295948200762766424915 / 18719953867715375029456 * μ ^ 3 + 32861551427443262555125 /
    74879815470861500117824 * μ ^ 4), 3, 1, 0), ((1613468395031651362069777 /
    3743990773543075005891200 - 1143219387809744489357889 / 187199538677153750294560 * μ +
    281515962400703127063185 / 74879815470861500117824 * μ ^ 2 - 43583790958782796279595 /
    37439907735430750058912 * μ ^ 3 + 115675150075720177053625 / 149759630941723000235648 * μ ^ 4),
    2, 2, 0), ((118182906388714479292059 / 1871995386771537502945600 - 296107058988911239921213 /
    93599769338576875147280 * μ + 112079934460141702851445 / 37439907735430750058912 * μ ^ 2 -
    24321743595311438589065 / 18719953867715375029456 * μ ^ 3 + 92483703797318343589375 /
    74879815470861500117824 * μ ^ 4), 1, 3, 0), ((-245446785945058432150291 /
    7487981547086150011782400 - 332388749621900081418513 / 374399077354307500589120 * μ +
    247606316520919372109345 / 149759630941723000235648 * μ ^ 2 - 53744279526938075800015 /
    74879815470861500117824 * μ ^ 3 + 335905305286433500182125 / 299519261883446000471296 * μ ^ 4),
    0, 4, 0)]

/-- The weight-five truncation of `x₂²`, degree five. -/
def lowQL5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((23214357583787623369290263376703398137 /
    27709447086086921900860971994439262000 + 20793089314685479673705208989406757249 /
    11822697423397086677700681384294085120 * μ - 16433604805926766647517173519599538907 /
    23645394846794173355401362768588170240 * μ ^ 2 + 10218998796781342659397515100989200009 /
    18029613570680557183493539111048479808 * μ ^ 3 - 9179738177370622670644468739970004655 /
    11095146812726496728303716376029833728 * μ ^ 4 - 20770474730812643917640106900585536725 /
    144236908565444457467948312888387838464 * μ ^ 5 - 64584804306330000043175497634139137875 /
    288473817130888914935896625776775676928 * μ ^ 6), 5, 0, 0),
    ((583046509098813389645122629411318529 / 692736177152173047521524299860981550 +
    30934140166302925390252410321919293563 / 7093618454038252006620408830576451072 * μ -
    39302934921870004903793184317363567561 / 14187236908076504013240817661152902144 * μ ^ 2 +
    40890505046154502377563009922662744075 / 18029613570680557183493539111048479808 * μ ^ 3 -
    15640782537284915552453665348964773075 / 11095146812726496728303716376029833728 * μ ^ 4 +
    6379440271752625399084612329913373375 / 144236908565444457467948312888387838464 * μ ^ 5 -
    15204249533541097608483776509876654375 / 288473817130888914935896625776775676928 * μ ^ 6), 4, 1,
    0), ((6558561576298438792693080059542579823 / 11083778834434768760344388797775704800 +
    21611708782890752021150744204355474727 / 3546809227019126003310204415288225536 * μ -
    19833045624828721310491464128645905171 / 7093618454038252006620408830576451072 * μ ^ 2 +
    102219252218650937939034289510110471935 / 18029613570680557183493539111048479808 * μ ^ 3 -
    1610287704897463443340011310705606625 / 426736415874096028011681399078070528 * μ ^ 4 +
    34779435840941712901321839755168885375 / 72118454282722228733974156444193919232 * μ ^ 5 -
    129596133635777714987540268714827363125 / 144236908565444457467948312888387838464 * μ ^ 6), 3,
    2, 0), ((5569875315333906572798805422456049433 / 11083778834434768760344388797775704800 +
    6109869677821172853934527796308730233 / 1182269742339708667770068138429408512 * μ -
    5600703602427272932222012902487535117 / 2364539484679417335540136276858817024 * μ ^ 2 +
    113314020297431603433809401735630748195 / 18029613570680557183493539111048479808 * μ ^ 3 -
    32646425679154633252812929824689072425 / 5547573406363248364151858188014916864 * μ ^ 4 +
    29703490713774257455231308159523339875 / 72118454282722228733974156444193919232 * μ ^ 5 -
    190466799326155164373375762222440690625 / 144236908565444457467948312888387838464 * μ ^ 6), 2,
    3, 0), ((1452760100426418048120752341088221 / 5686905507662785408078188197935200 +
    14668037726563741446033054488039789839 / 7093618454038252006620408830576451072 * μ +
    3063662540579038566314855848718223599 / 14187236908076504013240817661152902144 * μ ^ 2 +
    28369695622786323675103411262642449045 / 9014806785340278591746769555524239904 * μ ^ 3 -
    47426220109453490282413082403981629475 / 11095146812726496728303716376029833728 * μ ^ 4 +
    62588777447470509769032202947534786875 / 144236908565444457467948312888387838464 * μ ^ 5 -
    423186776447631838585980204660874199375 / 288473817130888914935896625776775676928 * μ ^ 6), 1,
    4, 0), ((4443943343257553803589102822249129549 / 55418894172173843801721943988878524000 +
    537122611357576855849896882269080327 / 865075421224177073978098637875176960 * μ +
    33351619968859848611303367122913040879 / 70936184540382520066204088305764510720 * μ ^ 2 +
    5705338702488330545566834063203581941 / 4507403392670139295873384777762119952 * μ ^ 3 -
    35883432743543940031442060495566988455 / 11095146812726496728303716376029833728 * μ ^ 4 +
    76658299370036732989093525716614467775 / 144236908565444457467948312888387838464 * μ ^ 5 -
    505029157792411289411632442422872527875 / 288473817130888914935896625776775676928 * μ ^ 6), 0,
    5, 0)]

/-- The jet of the first chart coordinate, degree 2. -/
def cF2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-37147 / 110545 + 961 / 44218 * μ - 1535 / 22109 * μ ^
    2), 2, 0, 0), ((-6754 / 110545 - 34 / 22109 * μ - 3070 / 22109 * μ ^ 2), 1, 1, 0), ((-307 /
    110545 - 1029 / 44218 * μ - 1535 / 22109 * μ ^ 2), 0, 2, 0)]

/-- The jet of the second chart coordinate, degree 2. -/
def cG2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((27104 / 22109 + 44817 / 44218 * μ + 5600 / 22109 * μ ^
    2), 2, 0, 0), ((4928 / 22109 + 26482 / 22109 * μ + 11200 / 22109 * μ ^ 2), 1, 1, 0), ((224 /
    22109 + 8147 / 44218 * μ + 5600 / 22109 * μ ^ 2), 0, 2, 0)]

/-- The jet of the first chart coordinate, degree 3. -/
def cF3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-85191236974723 / 802573659813900 - 129604009223567 /
    428039285234080 * μ + 4831751266461 / 42803928523408 * μ ^ 2 - 3617963686185 / 85607857046816 *
    μ ^ 3 + 472798212775 / 21401964261704 * μ ^ 4), 3, 0, 0), ((-19479179631393 / 267524553271300 -
    124369452344171 / 428039285234080 * μ + 8360095501013 / 42803928523408 * μ ^ 2 - 10047891863605
    / 85607857046816 * μ ^ 3 + 1083554036325 / 21401964261704 * μ ^ 4), 2, 1, 0), ((-12276562850863
    / 267524553271300 + 7557661958409 / 428039285234080 * μ + 4832472952093 / 42803928523408 * μ ^ 2
    - 10359724221905 / 85607857046816 * μ ^ 3 + 1934607233075 / 21401964261704 * μ ^ 4), 1, 2, 0),
    ((-2929204075133 / 802573659813900 + 13237912723513 / 428039285234080 * μ + 2246724615041 /
    42803928523408 * μ ^ 2 - 2392383236985 / 85607857046816 * μ ^ 3 + 1323851409525 / 21401964261704
    * μ ^ 4), 0, 3, 0)]

/-- The jet of the second chart coordinate, degree 3. -/
def cG3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-396715552556389 / 802573659813900 + 88002303300989 /
    428039285234080 * μ - 336190057733 / 3292609886416 * μ ^ 2 - 93074088205 / 85607857046816 * μ ^
    3 - 215608305500 / 2675245532713 * μ ^ 4), 3, 0, 0), ((6744931303601 / 267524553271300 +
    135746952759777 / 428039285234080 * μ - 406659690369 / 3292609886416 * μ ^ 2 + 19724911389335 /
    85607857046816 * μ ^ 3 - 494128876500 / 2675245532713 * μ ^ 4), 2, 1, 0), ((38940262672691 /
    267524553271300 - 253145568550763 / 428039285234080 * μ - 163812127789 / 3292609886416 * μ ^ 2 +
    884379837035 / 85607857046816 * μ ^ 3 - 882231311500 / 2675245532713 * μ ^ 4), 1, 2, 0),
    ((10154783669881 / 802573659813900 - 44137599091051 / 428039285234080 * μ - 652552437653 /
    3292609886416 * μ ^ 2 + 9396508756995 / 85607857046816 * μ ^ 3 - 603710740500 / 2675245532713 *
    μ ^ 4), 0, 3, 0)]

/-- The jet of the first chart coordinate, degree 4. -/
def cF4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((823436812702714734162492208 /
    9700299845187169371708813375 + 16881074459580595055230362151 / 124163838018395767957872811200 *
    μ - 1770080725530035691199200199 / 33110356804905538122099416320 * μ ^ 2 +
    134297858879227266199862207 / 827758920122638453052485408 * μ ^ 3 - 64917077543216057968268375 /
    3311035680490553812209941632 * μ ^ 4 + 34638125685898769942541925 / 1655517840245276906104970816
    * μ ^ 5 + 27906053495228904004773125 / 6622071360981107624419883264 * μ ^ 6), 4, 0, 0),
    ((77380210714600362232745723 / 38801199380748677486835253500 + 1158659907399019365814108561 /
    31040959504598941989468202800 * μ + 90244813814093925323111201 / 8277589201226384530524854080 *
    μ ^ 2 + 82957226619537279337142167 / 206939730030659613263121352 * μ ^ 3 -
    95660993891002416837390075 / 827758920122638453052485408 * μ ^ 4 + 22509503817643637444053925 /
    413879460061319226526242704 * μ ^ 5 - 50442481441125408022116875 / 1655517840245276906104970816
    * μ ^ 6), 3, 1, 0), ((-709524457210478614241056207 / 25867466253832451657890169000 +
    848791770025574462977130221 / 20693973003065961326312135200 * μ + 700726255377077785229555653 /
    16555178402452769061049708160 * μ ^ 2 + 355204394077508437033950487 /
    827758920122638453052485408 * μ ^ 3 - 371816456187496989576195075 / 1655517840245276906104970816
    * μ ^ 4 + 1579599850882288359159325 / 25867466253832451657890169 * μ ^ 5 -
    177561355366230471777314375 / 3311035680490553812209941632 * μ ^ 6), 2, 2, 0),
    ((-174442322099939716647259303 / 9700299845187169371708813375 - 1325798290001257887322483369 /
    31040959504598941989468202800 * μ + 24507019398221773991104411 / 201892419542106939768898880 * μ
    ^ 2 + 54324552753936223213468399 / 413879460061319226526242704 * μ ^ 3 -
    118715367143939274882270725 / 827758920122638453052485408 * μ ^ 4 + 15579965233535448428533025 /
    206939730030659613263121352 * μ ^ 5 - 141962485328883657409690625 / 1655517840245276906104970816
    * μ ^ 6), 1, 3, 0), ((-181479831399191806936855771 / 77602398761497354973670507000 -
    315577847355522374736095209 / 124163838018395767957872811200 * μ + 1046259788858299223031499601
    / 33110356804905538122099416320 * μ ^ 2 + 4277498705378437886408261 /
    413879460061319226526242704 * μ ^ 3 - 300155478551091668087622175 / 3311035680490553812209941632
    * μ ^ 4 + 28589789116567074340491175 / 1655517840245276906104970816 * μ ^ 5 -
    515614643614675422779561875 / 6622071360981107624419883264 * μ ^ 6), 0, 4, 0)]

/-- The jet of the second chart coordinate, degree 4. -/
def cG4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-17700966336966663076383785063 /
    31040959504598941989468202800 - 464395918496858610570980533633 / 248327676036791535915745622400
    * μ - 989741040942050161557659039 / 2069397300306596132631213520 * μ ^ 2 -
    565405447022867382421426091 / 827758920122638453052485408 * μ ^ 3 - 13997172048193238214289465 /
    827758920122638453052485408 * μ ^ 4 - 401492432326002090415897725 / 3311035680490553812209941632
    * μ ^ 5 - 3181471896850200782303125 / 206939730030659613263121352 * μ ^ 6), 4, 0, 0),
    ((-532798447677442040483856892 / 1940059969037433874341762675 - 98540278133561969504753020393 /
    62081919009197883978936405600 * μ - 2503161861674323520271397041 / 2069397300306596132631213520
    * μ ^ 2 - 202193909121721609353531561 / 206939730030659613263121352 * μ ^ 3 +
    132887090065634594254561995 / 413879460061319226526242704 * μ ^ 4 + 15651995073182531931891275 /
    827758920122638453052485408 * μ ^ 5 + 5750771499802570947146875 / 51734932507664903315780338 * μ
    ^ 6), 3, 1, 0), ((-63871475308231838875823556 / 646686656345811291447254225 -
    28112623615856562917907522303 / 41387946006131922652624270400 * μ - 756903372749449276857244207
    / 1034698650153298066315606760 * μ ^ 2 - 1251788369537412290283482061 /
    827758920122638453052485408 * μ ^ 3 + 20436782228946079806910430 / 25867466253832451657890169 *
    μ ^ 4 - 306904802258201822609131675 / 1655517840245276906104970816 * μ ^ 5 +
    20243151263251030984384375 / 103469865015329806631560676 * μ ^ 6), 2, 2, 0),
    ((273938176984114843493050547 / 7760239876149735497367050700 - 6708092148221976140474027363 /
    62081919009197883978936405600 * μ - 1101059856785721027739662861 / 2069397300306596132631213520
    * μ ^ 2 - 62617652594715836387962377 / 413879460061319226526242704 * μ ^ 3 +
    174984169740170368399833845 / 413879460061319226526242704 * μ ^ 4 + 126834336217667240684171775
    / 827758920122638453052485408 * μ ^ 5 + 16184648164530710128140625 / 51734932507664903315780338
    * μ ^ 6), 1, 3, 0), ((224635026198666323568252667 / 31040959504598941989468202800 -
    5807293336092854947981006073 / 248327676036791535915745622400 * μ - 129926053301793903857131199
    / 2069397300306596132631213520 * μ ^ 2 - 6277099198106050237427131 / 51734932507664903315780338
    * μ ^ 3 + 309422484496587096371509885 / 827758920122638453052485408 * μ ^ 4 -
    312190055010597553245524225 / 3311035680490553812209941632 * μ ^ 5 + 58783428425125862531871875
    / 206939730030659613263121352 * μ ^ 6), 0, 4, 0)]

/-- The jet of the first chart coordinate, degree 5. -/
def cF5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((3026237970397718632812936502951838241356917 /
    61262816562629575630613522982505764355800000 + 1548334410630804383726894348211039892042631 /
    4901025325010366050449081838600461148464000 * μ + 566145472262208434958661412745374196981251 /
    15683281040033171361437061883521475675084800 * μ ^ 2 -
    24983268985039209211926060474951979950120617 / 382672057376809381219064309957924006472069120 * μ
    ^ 3 + 148185590354866064975333070462518295405673 / 6377867622946823020317738499298733441201152 *
    μ ^ 4 - 27237550718417128721656440660838957379755 / 981210403530280464664267461430574375569408 *
    μ ^ 5 + 631671893248779930071182118443140591753075 /
    12755735245893646040635476998597466882402304 * μ ^ 6 +
    277861338593978441603068988692772383909625 / 25511470491787292081270953997194933764804608 * μ ^
    7 + 99137674610216550066274388868403576638125 / 6377867622946823020317738499298733441201152 * μ
    ^ 8), 5, 0, 0), ((382307014253753788049369380989381219142847 /
    12252563312525915126122704596501152871160000 + 30760072850175383460499885499168640691153 /
    98020506500207321008981636772009222969280 * μ + 232293663734309501868728356197590276026769 /
    3136656208006634272287412376704295135016960 * μ ^ 2 -
    21630190408573568745515797973419867168616459 / 76534411475361876243812861991584801294413824 * μ
    ^ 3 + 3035848875478307189544435939864887094578455 / 19133602868840469060953215497896200323603456
    * μ ^ 4 - 2134153974107766498963179573594573908738225 /
    12755735245893646040635476998597466882402304 * μ ^ 5 +
    1327720436986608709903841447584946192324125 / 12755735245893646040635476998597466882402304 * μ ^
    6 + 104399590671169920065476731362284415354375 / 25511470491787292081270953997194933764804608 *
    μ ^ 7 + 23338523033985584829022596942660664465625 / 6377867622946823020317738499298733441201152
    * μ ^ 8), 4, 1, 0), ((107392296812469042436146166102303862526227 /
    6126281656262957563061352298250576435580000 + 9012163468406678966555001556114397063657 /
    40841877708419717087075681988337176237200 * μ - 167223111817502837231153785833288545378293 /
    1568328104003317136143706188352147567508480 * μ ^ 2 -
    6549751103585729860146513941745943392457151 / 38267205737680938121906430995792400647206912 * μ ^
    3 - 457800212535502924585599560824507972396285 / 9566801434420234530476607748948100161801728 * μ
    ^ 4 - 2232769642724763166667441935651148066338625 / 6377867622946823020317738499298733441201152
    * μ ^ 5 + 1332350388810502040813249186011794001907875 /
    6377867622946823020317738499298733441201152 * μ ^ 6 - 31102709048684120503898252665634763150625
    / 981210403530280464664267461430574375569408 * μ ^ 7 +
    198930065130918792505874312477260002396875 / 3188933811473411510158869249649366720600576 * μ ^
    8), 3, 2, 0), ((-31992125964606908326769057251903776467443 /
    6126281656262957563061352298250576435580000 + 6116209755325786666264788740406741728021 /
    61262816562629575630613522982505764355800 * μ - 50623862234000716991936012351797570795807 /
    313665620800663427228741237670429513501696 * μ ^ 2 -
    10231956920916630816064793979680094601951393 / 38267205737680938121906430995792400647206912 * μ
    ^ 3 - 97602960705485078876841177879834234478375 / 3188933811473411510158869249649366720600576 *
    μ ^ 4 - 14897879055816021343345960262927067277975 / 37738861674241556333241056208868245214208 *
    μ ^ 5 + 2469651347813134835790647936838441247479125 /
    6377867622946823020317738499298733441201152 * μ ^ 6 + 167680956663031721465412096723679665798125
    / 12755735245893646040635476998597466882402304 * μ ^ 7 +
    292366536965648177313131795011446460109375 / 3188933811473411510158869249649366720600576 * μ ^
    8), 2, 3, 0), ((-79550998483331655686799939767471369080163 /
    12252563312525915126122704596501152871160000 + 1788532008097544214034377040022347602989 /
    75400389615544093083832028286160940745600 * μ - 185061760870594583881714762132419083852057 /
    3136656208006634272287412376704295135016960 * μ ^ 2 -
    3816129571781921452779886807828451091012385 / 76534411475361876243812861991584801294413824 * μ ^
    3 - 3887533078376433552454174126065229486491565 / 19133602868840469060953215497896200323603456 *
    μ ^ 4 - 1528555850807223321035391301711684427035675 /
    12755735245893646040635476998597466882402304 * μ ^ 5 +
    229732770769895929864187985499514234216375 / 981210403530280464664267461430574375569408 * μ ^ 6
    - 452465420181437656369210335848462822626875 / 25511470491787292081270953997194933764804608 * μ
    ^ 7 + 649591701847114872229479614154441896040625 / 6377867622946823020317738499298733441201152 *
    μ ^ 8), 1, 4, 0), ((-67873707351842217142538259625663415896433 /
    61262816562629575630613522982505764355800000 - 1546119870241465159257598078811417916429 /
    816837554168394341741513639766743524744000 * μ - 312961341009026107225217061194354355680459 /
    15683281040033171361437061883521475675084800 * μ ^ 2 -
    19683137283342189071236680345399422660582827 / 382672057376809381219064309957924006472069120 * μ
    ^ 3 - 1464228290719562591276327709587109544525321 / 19133602868840469060953215497896200323603456
    * μ ^ 4 + 114095907674914176403394661122564246169035 /
    12755735245893646040635476998597466882402304 * μ ^ 5 +
    2605056022139872505486366292878892246224325 / 12755735245893646040635476998597466882402304 * μ ^
    6 + 28315215865739083644071567751146006772375 / 1962420807060560929328534922861148751138816 * μ
    ^ 7 + 775219757211351329246855799119109330288125 / 6377867622946823020317738499298733441201152 *
    μ ^ 8), 0, 5, 0)]

/-- The jet of the second chart coordinate, degree 5. -/
def cG5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-2707089247823137321265169806920186714589613 /
    20420938854209858543537840994168588118600000 - 379038121653422979621569002237936324526721 /
    408418777084197170870756819883371762372000 * μ - 490708656565937397214826039192616614007771 /
    5227760346677723787145687294507158558361600 * μ ^ 2 +
    36548380596064125192356332786438000142961523 / 382672057376809381219064309957924006472069120 * μ
    ^ 3 - 88005496209062402736988566768325562463723 / 1594466905736705755079434624824683360300288 *
    μ ^ 4 - 313846515829594800407513710611216514221855 / 981210403530280464664267461430574375569408
    * μ ^ 5 - 3242378207605810979548841431605478684215125 /
    12755735245893646040635476998597466882402304 * μ ^ 6 -
    4011977509189607521319755042153708151741875 / 25511470491787292081270953997194933764804608 * μ ^
    7 - 11302340753607750007555712085974349128125 / 199308363217088219384929328103085420037536 * μ ^
    8), 5, 0, 0), ((-784298098678520739970766097755367606085983 /
    4084187770841971708707568198833717623720000 - 1527266784900217842453144607248501261746491 /
    980205065002073210089816367720092229692800 * μ - 1155794289248699074533252020055413282351131 /
    3136656208006634272287412376704295135016960 * μ ^ 2 +
    37827105836724395926813046921219061752742435 / 25511470491787292081270953997194933764804608 * μ
    ^ 3 - 1891209259489884624389593922105822188761655 / 4783400717210117265238303874474050080900864
    * μ ^ 4 + 10224660799084244871279613907254023389263875 /
    12755735245893646040635476998597466882402304 * μ ^ 5 -
    5021083649050095637910593340472086999323875 / 12755735245893646040635476998597466882402304 * μ ^
    6 + 2828827946131914646057454339800811428581875 / 25511470491787292081270953997194933764804608 *
    μ ^ 7 - 2660743668369692081484660889228414515625 / 199308363217088219384929328103085420037536 *
    μ ^ 8), 4, 1, 0), ((-1129696757538462557056885297140740865743209 /
    6126281656262957563061352298250576435580000 - 114087395077401272266586917473888347194963 /
    98020506500207321008981636772009222969280 * μ + 1380456707730453842413025349320752731099271 /
    1568328104003317136143706188352147567508480 * μ ^ 2 +
    56015815254691562002811478614515679964785237 / 38267205737680938121906430995792400647206912 * μ
    ^ 3 + 4460548344670624319381045608989872072324045 / 4783400717210117265238303874474050080900864
    * μ ^ 4 - 133704845870114755661545702856577621578925 /
    6377867622946823020317738499298733441201152 * μ ^ 5 -
    5226801445957035905418147902965728985652125 / 6377867622946823020317738499298733441201152 * μ ^
    6 - 123143124968240781757199565530161781845625 / 311115493802284049771596999965791875180544 * μ
    ^ 7 - 22679323386261100122819547025094788546875 / 99654181608544109692464664051542710018768 * μ
    ^ 8), 3, 2, 0), ((-144119397291152210468508810262473116409373 /
    2042093885420985854353784099416858811860000 - 114699041016414275161182082698132259241783 /
    163367510833678868348302727953348704948800 * μ + 447940627560606026737748349445107081498931 /
    522776034667772378714568729450715855836160 * μ ^ 2 +
    65728048314322796158838163377673050512886219 / 38267205737680938121906430995792400647206912 * μ
    ^ 3 + 257194734821232065154873007522706810020625 / 1594466905736705755079434624824683360300288 *
    μ ^ 4 + 720298055410574327628454836345449952591425 / 490605201765140232332133730715287187784704
    * μ ^ 5 - 10727243651039076730488852724920928747247875 /
    6377867622946823020317738499298733441201152 * μ ^ 6 + 815510162982995849785755339913536314970625
    / 12755735245893646040635476998597466882402304 * μ ^ 7 -
    33331689882077153765340758388927120859375 / 99654181608544109692464664051542710018768 * μ ^ 8),
    2, 3, 0), ((11586716473228923737130136265891295002107 /
    4084187770841971708707568198833717623720000 - 2566993732096550942955552949109899870199 /
    11953720304903331830363614240488929630400 * μ + 235622213971504277165011292690133658598567 /
    627331241601326854457482475340859027003392 * μ ^ 2 +
    22298757609327175903810572673047557758874217 / 25511470491787292081270953997194933764804608 * μ
    ^ 3 + 1782359270712029182028295119477061061481045 / 2391700358605058632619151937237025040450432
    * μ ^ 4 - 5248305414249470824950041231428225520033775 /
    12755735245893646040635476998597466882402304 * μ ^ 5 -
    11962657485310221259219091285330718217486125 / 12755735245893646040635476998597466882402304 * μ
    ^ 6 - 1101129645972077122745737448365746456941875 / 1962420807060560929328534922861148751138816
    * μ ^ 7 - 74057685878335571752546535815652984890625 / 199308363217088219384929328103085420037536
    * μ ^ 8), 1, 4, 0), ((171679143252196382564670962681190269426611 /
    61262816562629575630613522982505764355800000 - 70798308600384578542903887409115006464447 /
    4901025325010366050449081838600461148464000 * μ + 841040111303184322195408323089233492946297 /
    15683281040033171361437061883521475675084800 * μ ^ 2 +
    94454465821854893480746114686636253864803433 / 382672057376809381219064309957924006472069120 * μ
    ^ 3 + 434740645355838042769304967024252452666123 / 2391700358605058632619151937237025040450432 *
    μ ^ 4 + 1472236077917446386523281107780850262908335 /
    12755735245893646040635476998597466882402304 * μ ^ 5 -
    10281326762260279401236501478851906918560875 / 12755735245893646040635476998597466882402304 * μ
    ^ 6 + 182731949743985468980834302025225166274375 / 25511470491787292081270953997194933764804608
    * μ ^ 7 - 88380102613671975647035677424002692378125 / 199308363217088219384929328103085420037536
    * μ ^ 8), 0, 5, 0)]

/-- The polynomial part of the defect, degrees five to eight. -/
def highD (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((3153195738168791798360908105431104677379 /
    147266385967859556804359430246408087393750 + 2091823597645315852099355247925213852752487 /
    6126281656262957563061352298250576435580000 * μ + 221431261991670999624756124083247626737127 /
    816837554168394341741513639766743524744000 * μ ^ 2 + 30736414772497650072413711807742887281403 /
    163367510833678868348302727953348704948800 * μ ^ 3 + 35628284785353004199534625463605459427663 /
    98020506500207321008981636772009222969280 * μ ^ 4 + 15040774932022001557924015963558135933 /
    125667316025906821806386713810268234576 * μ ^ 5 + 822647342646099399355424569025886766225 /
    6534700433347154733932109118133948197952 * μ ^ 6 + 317167840008541389359384214421156230275 /
    6534700433347154733932109118133948197952 * μ ^ 7 + 7139014460264112694473285147717938375 /
    502669264103627287225546855241072938304 * μ ^ 8), 5, 0, 0),
    ((55326356275413555164567848555089556229963 / 1531570414065739390765338074562644108895000 +
    1170417050906431368679401582676740847026793 / 1225256331252591512612270459650115287116000 * μ +
    494464153952701612684842278840767248752473 / 490102532501036605044908183860046114846400 * μ ^ 2
    + 1698985025187295082482056811093837840259 / 1531570414065739390765338074562644108895 * μ ^ 3 -
    1364522533007580704037089193838255400647 / 6534700433347154733932109118133948197952 * μ ^ 4 -
    2174158955849659980090041483506452388685 / 3267350216673577366966054559066974098976 * μ ^ 5 -
    4357253592147341311208419833075878083075 / 6534700433347154733932109118133948197952 * μ ^ 6 -
    447298652181569583154366528392604205875 / 1633675108336788683483027279533487049488 * μ ^ 7 -
    477624474520991954585224806577624770625 / 6534700433347154733932109118133948197952 * μ ^ 8), 4,
    1, 0), ((3056863781267041049985174376082743997774 / 63815433919405807948555753106776837870625 +
    74869629845256675331886734991176351633983 / 204209388542098585435378409941685881186000 * μ +
    5704372279478488931318456427882765222919 / 3267350216673577366966054559066974098976 * μ ^ 2 +
    14241077713889811972590136945060593312077 / 12252563312525915126122704596501152871160 * μ ^ 3 +
    5411015086499379330584294778064579762835 / 4901025325010366050449081838600461148464 * μ ^ 4 -
    118629443993892696339527951707872196235 / 102104694271049292717689204970842940593 * μ ^ 5 -
    2272031095245175081539666646783211690525 / 3267350216673577366966054559066974098976 * μ ^ 6 -
    47645239025788373196825250924069719625 / 125667316025906821806386713810268234576 * μ ^ 7 -
    166515791535928156709007163981170701875 / 816837554168394341741513639766743524744 * μ ^ 8), 3,
    2, 0), ((-19089408466259839709971517683921077730223 / 191446301758217423845667259320330513611875
    + 16042424342305087201731646678830084396443 / 61262816562629575630613522982505764355800 * μ +
    171106499973127899085025858264877803018079 / 81683755416839434174151363976674352474400 * μ ^ 2 +
    3124531894913492021527375456266340117401 / 1633675108336788683483027279533487049488 * μ ^ 3 -
    2077352346998232301419925075647560116277 / 4901025325010366050449081838600461148464 * μ ^ 4 -
    2147837796846036415017616300991112801935 / 1633675108336788683483027279533487049488 * μ ^ 5 -
    7117513908582389319271648351108212903725 / 3267350216673577366966054559066974098976 * μ ^ 6 -
    86785226500505581020684998836263675375 / 102104694271049292717689204970842940593 * μ ^ 7 -
    290106513658083302889199782451386849375 / 816837554168394341741513639766743524744 * μ ^ 8), 2,
    3, 0), ((-7197901120397168124266463643605193823269 / 191446301758217423845667259320330513611875
    + 64257730734539276444899321716457922162711 / 1225256331252591512612270459650115287116000 * μ +
    399286793782342791933653871150638564390909 / 490102532501036605044908183860046114846400 * μ ^ 2
    + 87569432181407170106570071025593914559867 / 98020506500207321008981636772009222969280 * μ ^ 3
    + 5003961285135989837539887742761202719779 / 6534700433347154733932109118133948197952 * μ ^ 4 -
    2804673235914124158755638560795801388855 / 1633675108336788683483027279533487049488 * μ ^ 5 -
    7514162255312049924300793208464041460175 / 6534700433347154733932109118133948197952 * μ ^ 6 -
    6701281828004154005724227389567792569375 / 6534700433347154733932109118133948197952 * μ ^ 7 -
    3746574005285287557036336164330619696875 / 6534700433347154733932109118133948197952 * μ ^ 8), 1,
    4, 0), ((-6535304606860537358665432894460582046689 / 2552617356776232317942230124271073514825000
    + 6987186487566392314349631960644006444089 / 2042093885420985854353784099416858811860000 * μ +
    82821876200549566562197843568089185000147 / 816837554168394341741513639766743524744000 * μ ^ 2 +
    20990888889549775406353985550253437005861 / 122525633125259151261227045965011528711600 * μ ^ 3 +
    15155933424200621531179571348380832616293 / 98020506500207321008981636772009222969280 * μ ^ 4 -
    362896227526511157615382433506646955417 / 3267350216673577366966054559066974098976 * μ ^ 5 -
    3821625804256671820520580910828898434475 / 6534700433347154733932109118133948197952 * μ ^ 6 -
    113553096006976328397272049001773053025 / 1633675108336788683483027279533487049488 * μ ^ 7 -
    2187416565803620967981417703070932547375 / 6534700433347154733932109118133948197952 * μ ^ 8), 0,
    5, 0), ((212566701903192343844745319012121575020046604239603 /
    4276706222942382285651417553650844473629571796500000 -
    2310906185862269920002781183174241318363536227574541 /
    17791097887440310308309897023187513010299018673440000 * μ -
    1807065506270247694788175232873666175836225674712027 /
    17791097887440310308309897023187513010299018673440000 * μ ^ 2 +
    137044878564668839704168332033694865369650092161331 /
    1581430923328027582960879735394445600915468326528000 * μ ^ 3 -
    3126273141600854434983534142226410229184947544743 /
    118607319249602068722065980154583420068660124489600 * μ ^ 4 +
    13165946089965030186477489248312360872302286966243 /
    63257236933121103318435189415777824036618733061120 * μ ^ 5 -
    81188721406127431348296781820642461099728858029 /
    1459782390764333153502350524979488246998893839872 * μ ^ 6 +
    811227597954654489787088706404955614501661768305 /
    12651447386624220663687037883155564807323746612224 * μ ^ 7 -
    105782506059426201594567366391641855996077947025 /
    3162861846656055165921759470788891201830936653056 * μ ^ 8 +
    54922741871639794333813289360167761853424438125 /
    12651447386624220663687037883155564807323746612224 * μ ^ 9 -
    3316052023001042047794864193334945121095540625 /
    486594130254777717834116841659829415666297946624 * μ ^ 10), 6, 0, 0),
    ((154521578269668361099075242716209181750295541297599 /
    1544366136062526936485234116596138282144012037625000 -
    1119206193499455147042107133087013885610636748485371 /
    2965182981240051718051649503864585501716503112240000 * μ -
    251246948824757530738673842868402881517095842020911 /
    1482591490620025859025824751932292750858251556120000 * μ ^ 2 -
    29099898117136939807888289914366302228614888839823 /
    121648532563694429458529210414957353916574486656000 * μ ^ 3 +
    75265172324253184251768350102593765430171813467651 /
    158143092332802758296087973539444560091546832652800 * μ ^ 4 -
    1183819529337128943389222238957989670090023508037 /
    14597823907643331535023505249794882469988938398720 * μ ^ 5 +
    386231716360288705726442180605820915462816548511 /
    2372146384992041374441319603091668401373202489792 * μ ^ 6 -
    806696374824625432217525119256774481261446291545 /
    12651447386624220663687037883155564807323746612224 * μ ^ 7 +
    455968691947901996593777464124731476711318828575 /
    6325723693312110331843518941577782403661873306112 * μ ^ 8 +
    17692866018771524780911034498364228324100176875 /
    973188260509555435668233683319658831332595893248 * μ ^ 9 +
    50543448239675074103206422432345831295630890625 /
    3162861846656055165921759470788891201830936653056 * μ ^ 10), 5, 1, 0),
    ((219095906740035984530354187249809252017463851383659 /
    3706478726550064647564561879830731877145628890300000 -
    1082545451952374565165557867883689516001296330447 /
    6082426628184721472926460520747867695828724332800 * μ -
    861162808969769459802461408088996094479993987281209 /
    2372146384992041374441319603091668401373202489792000 * μ ^ 2 -
    26078871006627176332569465128019002551061194034899 /
    237214638499204137444131960309166840137320248979200 * μ ^ 3 +
    8151170611099926800754710636861620301337877087997 /
    47442927699840827488826392061833368027464049795840 * μ ^ 4 -
    731057113438523135494274799419931821757005498197 /
    9488585539968165497765278412366673605492809959168 * μ ^ 5 -
    160159862976391440522295659028564627837190432355 /
    3162861846656055165921759470788891201830936653056 * μ ^ 6 -
    1039351619867454972191598381785738499135491903825 /
    3162861846656055165921759470788891201830936653056 * μ ^ 7 +
    435432352902680305030633584087622252142432470875 /
    3162861846656055165921759470788891201830936653056 * μ ^ 8 -
    44582077655816844299554904874478721043346778125 /
    790715461664013791480439867697222800457734163264 * μ ^ 9 +
    200664437988974261415536144742993199106202765625 /
    6325723693312110331843518941577782403661873306112 * μ ^ 10), 4, 2, 0),
    ((13181849532691598761401947131070216795369829778648 /
    347482380614068560709177676234131113482402708465625 -
    38723391396836809048567333023764778208443926257483 /
    889554894372015515415494851159375650514950933672000 * μ -
    2864443680689263660638986546182402370649895828002073 /
    3558219577488062061661979404637502602059803734688000 * μ ^ 2 +
    36129905997854024943426417479151705067780629555541 /
    474429276998408274888263920618333680274640497958400 * μ ^ 3 +
    913191680034119598903963422172417938364647005183 /
    23721463849920413744413196030916684013732024897920 * μ ^ 4 +
    2404315346302833474814709223920378402236698839871 /
    6325723693312110331843518941577782403661873306112 * μ ^ 5 +
    479634240526663186643109451242853828184345602635 /
    3162861846656055165921759470788891201830936653056 * μ ^ 6 -
    531715280618592989518809975651613653417502883575 /
    6325723693312110331843518941577782403661873306112 * μ ^ 7 +
    317749692524781635267013879771542234048705027375 /
    790715461664013791480439867697222800457734163264 * μ ^ 8 +
    462528654907836327157374789383550420536637140625 /
    6325723693312110331843518941577782403661873306112 * μ ^ 9 +
    293133652061066863768518883402188404827171875 / 1900758321307725460289518912733708654946476354 *
    μ ^ 10), 3, 3, 0), ((-6995401211414117521030079365457346995211116633227 /
    1235492908850021549188187293276910625715209630100000 +
    16190772847996027170293189560008996588893907744443 /
    237214638499204137444131960309166840137320248979200 * μ -
    88633288048598282004315583185214187521383054351041 /
    593036596248010343610329900772917100343300622448000 * μ ^ 2 -
    3008270097161438279305162024643773125144868307009 /
    24329706512738885891705842082991470783314897331200 * μ ^ 3 -
    145385905480222927291354141182622140744906165341 /
    608242662818472147292646052074786769582872433280 * μ ^ 4 -
    14327154447923229628525789593524264328141695120743 /
    37954342159872661991061113649466694421971239836672 * μ ^ 5 +
    225501594122933098384202458775461962794330624615 /
    1459782390764333153502350524979488246998893839872 * μ ^ 6 -
    837527733559017682902900951615300193118724299975 /
    973188260509555435668233683319658831332595893248 * μ ^ 7 +
    2060360099109955881668447913605395102354381773375 /
    3162861846656055165921759470788891201830936653056 * μ ^ 8 -
    1929500101274647109716156666627614779519020034375 /
    12651447386624220663687037883155564807323746612224 * μ ^ 9 +
    1291677514000672921372724224642975882069482828125 /
    6325723693312110331843518941577782403661873306112 * μ ^ 10), 2, 4, 0),
    ((-45814420639527449530398125554607219430109647564643 /
    4633098408187580809455702349788414846432036112875000 +
    90250290783676354122030872563941936250977142115523 /
    988394327080017239350549834621528500572167704080000 * μ -
    619483109799293822500433277006170410982112174459629 /
    5930365962480103436103299007729171003433006224480000 * μ ^ 2 -
    2208638196600216062062439018582953907963898447559717 /
    4744292769984082748882639206183336802746404979584000 * μ ^ 3 -
    214641526895858218275733875311845165289052851336657 /
    474429276998408274888263920618333680274640497958400 * μ ^ 4 +
    133049167184977477440343452804856531473663543725699 /
    189771710799363309955305568247333472109856199183360 * μ ^ 5 -
    1114746963406268682850139791904820292692368023027 /
    3162861846656055165921759470788891201830936653056 * μ ^ 6 +
    5242519763514168636332366327835795584431788670955 /
    12651447386624220663687037883155564807323746612224 * μ ^ 7 +
    2993480511931733242328097457084545649996122946325 /
    6325723693312110331843518941577782403661873306112 * μ ^ 8 +
    487762127558922114320203277162306865220092481875 /
    12651447386624220663687037883155564807323746612224 * μ ^ 9 +
    836014859526125887030456813864334509010961134375 /
    3162861846656055165921759470788891201830936653056 * μ ^ 10), 1, 5, 0),
    ((-45984665053162382950893534948366469426892486102981 /
    55597180898250969713468428197460978157184433354500000 +
    4525963534875040803191965161405542140176841047959 /
    433929216766836836788046268858232024641439479840000 * μ -
    304325943635509888473481524104383814612934163325719 /
    35582195774880620616619794046375026020598037346880000 * μ ^ 2 -
    313140588522640095263335442600840749683930916775831 /
    2372146384992041374441319603091668401373202489792000 * μ ^ 3 -
    10522335715341041114177815799058143807873691531677 /
    79071546166401379148043986769722280045773416326400 * μ ^ 4 +
    3081347463580703457550178655308762801805218851879 /
    31628618466560551659217594707888912018309366530560 * μ ^ 5 +
    341415737445229640170793748777098862680811374281 /
    2372146384992041374441319603091668401373202489792 * μ ^ 6 -
    62780370795778326636203444079420759714314173695 /
    486594130254777717834116841659829415666297946624 * μ ^ 7 +
    1585010325760096862106851530816462500024587512225 /
    3162861846656055165921759470788891201830936653056 * μ ^ 8 -
    666244312296646657433909304917641530049491883125 /
    6325723693312110331843518941577782403661873306112 * μ ^ 9 +
    1299432133900198808722030181683228897276568484375 /
    6325723693312110331843518941577782403661873306112 * μ ^ 10), 0, 6, 0)]

/-- `h`, degrees two to four. -/
def hL (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := hL2 μ ++ hL3 μ ++ hL4 μ

/-- The graph in chart coordinates, `H(y) = h(y) w`. -/
def manifoldH (μ : ℝ) (y : State 2) : State 3 := poly3 (hL μ) (y 0) (y 1) 0 • wsv

/-- **The order-four approximate centre manifold** `φ(x) = H(π x)` of the path. -/
def manifold (μ : ℝ) (x : State 3) : State 3 := manifoldH μ (critπ pC x)

/-- `π H(y) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critπ_manifoldH (μ : ℝ) (y : State 2) :
    critπ pC (manifoldH μ y) = 0 := by
  simp [manifoldH, map_smul, critπ_wsv]

/-- The derivative of `H`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_manifoldH (μ : ℝ) (y : State 2) :
    ∃ L : State 2 →L[ℝ] State 3, HasFDerivAt (manifoldH μ) L y ∧ ∀ v, L v =
      dpoly3 (hL μ) (y 0) (y 1) 0 (v 0) (v 1) 0 • wsv := by
  obtain ⟨L1, h1, hv1⟩ := Dynamics.Degenerate.hasFDerivAt_poly3 (hL μ) (Dynamics.coord 0)
    (Dynamics.coord 1) 0 y
  have e : manifoldH μ = fun z => poly3 (hL μ) (Dynamics.coord 0 z) (Dynamics.coord 1 z)
      ((0 : State 2 →L[ℝ] ℝ) z) • wsv := by
    funext z; simp [manifoldH]
  refine ⟨L1.smulRight wsv, ?_, fun v => ?_⟩
  · rw [e]; exact h1.smul_const wsv
  · simp [hv1]

/-- `φ` is `C¹`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem contDiffAt_manifold (μ : ℝ) : ContDiffAt ℝ 1 (manifold μ) 0 := by
  have h1 := Dynamics.Degenerate.contDiff_poly3 (hL μ) ((Dynamics.coord 0).comp (critπ pC))
    ((Dynamics.coord 1).comp (critπ pC)) 0 (k := 1)
  have e : manifold μ = fun x => poly3 (hL μ) ((Dynamics.coord 0).comp (critπ pC) x)
      ((Dynamics.coord 1).comp (critπ pC) x) ((0 : State 3 →L[ℝ] ℝ) x) • wsv := by
    funext x; simp [manifold, manifoldH]
  rw [e]
  exact (h1.smul contDiff_const).contDiffAt

/-- `φ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem manifold_zero (μ : ℝ) : manifold μ 0 = 0 := by
  simp [manifold, manifoldH, hL, hL2, hL3, hL4]

/-- `Dφ(0) = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fderiv_manifold_zero (μ : ℝ) : fderiv ℝ (manifold μ) 0 = 0 := by
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldH μ (critπ pC 0)
  have hc : HasFDerivAt (manifold μ) (L.comp (critπ pC)) 0 :=
    hL'.comp (0 : State 3) (critπ pC).hasFDerivAt
  rw [hc.fderiv]
  ext v i
  simp [hLv, hL, hL2, hL3, hL4]

/-- `φ` takes values in `ker P`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem critP_manifold (μ : ℝ) (x : State 3) :
    critP qC pC (manifold μ x) = 0 := by
  simp [critP, manifold, critπ_manifoldH]

/-! ## The chart field -/

/-- The point `ι y + H(y)` of the manifold over `y`. -/
def chartPt (μ : ℝ) (y : State 2) : State 3 := critι qC y + manifoldH μ y

/-- **The chart field** of the manifold: `rotL 1 y + π f(ι y + H y)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem chartField_eq (hμ : 0 < μ) (y : State 2) :
    chartField (fderiv ℝ (bpath μ).field 0) (fnl μ) (manifold μ) (critι qC) (critπ pC) y =
      rotL 1 y + critπ pC (fnl μ (chartPt μ y)) := by
  have hc := isCritical_C hμ
  rw [chartField, manifold, hc.critπ_critι, hc.apply_critι, map_add, hc.critπ_critι]
  rfl

/-- The linear part of the angle over `y`. -/
def lin0 (y : State 2) : ℝ := 11 / 5 * y 0 + 1 / 5 * y 1

/-- The linear part of `Q_f` over `y`. -/
def lin2 (y : State 2) : ℝ := -y 0 - y 1

/-- A planar polynomial at `y`. -/
def pv (L : List (ℝ × ℕ × ℕ × ℕ)) (y : State 2) : ℝ := poly3 L (y 0) (y 1) 0

/-- The angle `x₀` of the manifold over `y`. -/
def tv (μ : ℝ) (y : State 2) : ℝ := lin0 y + pv (aL2 μ) y + pv (aL3 μ) y + pv (aL4 μ) y

/-- The filtered reactive power `x₂` of the manifold over `y`. -/
def x2v (μ : ℝ) (y : State 2) : ℝ := lin2 y + pv (cL2 μ) y + pv (cL3 μ) y + pv (cL4 μ) y

/-- The angle and the filtered reactive power of `ι y + H(y)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem chartPt_apply (μ : ℝ) (y : State 2) :
    chartPt μ y 0 = tv μ y ∧ chartPt μ y 2 = x2v μ y := by
  refine ⟨?_, ?_⟩ <;>
    simp only [chartPt, PiLp.add_apply, critι_C, manifoldH, PiLp.smul_apply, smul_eq_mul,
      wsv, tv, x2v, lin0, lin2, pv, hL, hL2, hL3, hL4, aL2, aL3, aL4, cL2, cL3, cL4,
      poly3_cons, poly3_nil, List.cons_append, List.nil_append] <;>
    simp <;> ring

/-- The first chart coordinate of `f` on the manifold. -/
def G0 (μ : ℝ) (y : State 2) : ℝ := critπ pC (fnl μ (chartPt μ y)) 0

/-- The second chart coordinate of `f` on the manifold. -/
def G1 (μ : ℝ) (y : State 2) : ℝ := critπ pC (fnl μ (chartPt μ y)) 1

/-- The active-power nonlinearity on the manifold. -/
def F1v (μ : ℝ) (y : State 2) : ℝ :=
  -(122 / 85) * ((2 * μ + 5 * μ ^ 2) / 10 * (x2v μ y * x2v μ y) - (Real.cos (tv μ y) - 1) +
    1 / 2 * (Real.sin (tv μ y) - tv μ y) + μ * ((Real.cos (tv μ y) - 1) * x2v μ y) -
    μ / 2 * (Real.sin (tv μ y) * x2v μ y))

/-- The reactive-power nonlinearity on the manifold. -/
def F2v (μ : ℝ) (y : State 2) : ℝ :=
  (2 * μ + 5 * μ ^ 2) / 20 * (x2v μ y * x2v μ y) - 1 / 2 * (Real.cos (tv μ y) - 1) -
    (Real.sin (tv μ y) - tv μ y) + μ / 2 * ((Real.cos (tv μ y) - 1) * x2v μ y) +
    μ * (Real.sin (tv μ y) * x2v μ y)

/-- The nonlinearity at the manifold point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem fnl_chartPt (hμ : 0 < μ) (y : State 2) :
    fnl μ (chartPt μ y) 0 = 0 ∧ fnl μ (chartPt μ y) 1 = F1v μ y ∧
      fnl μ (chartPt μ y) 2 = F2v μ y := by
  obtain ⟨c0, c2⟩ := chartPt_apply μ y
  refine ⟨?_, ?_, ?_⟩ <;> rw [fnl_apply hμ] <;> simp [c0, c2, F1v, F2v]

/-- The chart coordinates of `f` on the manifold. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem G_eq (hμ : 0 < μ) (y : State 2) :
    G0 μ y = 3145 / 44218 * F1v μ y - 1626 / 22109 * F2v μ y ∧
      G1 μ y = -17595 / 44218 * F1v μ y - 2854 / 22109 * F2v μ y := by
  obtain ⟨f0, f1, f2⟩ := fnl_chartPt hμ y
  obtain ⟨g0, g1⟩ := critπ_C (fnl μ (chartPt μ y))
  rw [G0, G1, g0, g1, f0, f1, f2]
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
    (fun y : State 2 => lin0 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 := lin_isBigO (11 / 5) (1 / 5)

@[tmio M, powerlib_domain] private theorem o_l2 :
    (fun y : State 2 => lin2 y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
  (lin_isBigO (-1) (-1)).congr_left fun y => by simp only [lin2]; ring

section Pieces

variable (μ : ℝ)

@[tmio M, powerlib_domain] private theorem o_a2 :
   (fun y : State 2 => pv (aL2 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 pv_isBigO _ (by simp [aL2])

@[tmio M, powerlib_domain] private theorem o_a3 :
   (fun y : State 2 => pv (aL3 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 pv_isBigO _ (by simp [aL3])

@[tmio M, powerlib_domain] private theorem o_a4 :
   (fun y : State 2 => pv (aL4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
 pv_isBigO _ (by simp [aL4])

@[tmio M, powerlib_domain] private theorem o_c2 :
   (fun y : State 2 => pv (cL2 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 pv_isBigO _ (by simp [cL2])

@[tmio M, powerlib_domain] private theorem o_c3 :
   (fun y : State 2 => pv (cL3 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 pv_isBigO _ (by simp [cL3])

@[tmio M, powerlib_domain] private theorem o_c4 :
   (fun y : State 2 => pv (cL4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
 pv_isBigO _ (by simp [cL4])

@[tmio M, powerlib_domain] private theorem o_r :
   (fun y : State 2 => pv (aL2 μ) y + pv (aL3 μ) y + pv (aL4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 (((o_a2 μ).add (mono (o_a3 μ) (by norm_num))).add (mono (o_a4 μ) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_r3 :
   (fun y : State 2 => pv (aL3 μ) y + pv (aL4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 ((o_a3 μ).add (mono (o_a4 μ) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_C :
   (fun y : State 2 => pv (cL2 μ) y + pv (cL3 μ) y + pv (cL4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 2 :=
 (((o_c2 μ).add (mono (o_c3 μ) (by norm_num))).add (mono (o_c4 μ) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_C3 :
   (fun y : State 2 => pv (cL3 μ) y + pv (cL4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 3 :=
 ((o_c3 μ).add (mono (o_c4 μ) (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_u :
   (fun y : State 2 => tv μ y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
 (((o_l0.add (mono (o_a2 μ) (by norm_num))).add (mono (o_a3 μ) (by norm_num))).add (mono (o_a4 μ)
    (by norm_num)))

@[tmio M, powerlib_domain] private theorem o_X :
   (fun y : State 2 => x2v μ y) =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
 (((o_l2.add (mono (o_c2 μ) (by norm_num))).add (mono (o_c3 μ) (by norm_num))).add (mono (o_c4 μ)
    (by norm_num)))

end Pieces

/-! ## The nonlinearities minus their weight-five truncations -/

/-- The weight-five truncation of `cos x₀ − 1`. -/
def low2L (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := low2L4 μ ++ low2L5 μ

/-- The weight-five truncation of `sin x₀ − x₀`. -/
def low3L (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := low3L4 μ ++ low3L5 μ

/-- The weight-five truncation of `(cos x₀ − 1) x₂`. -/
def lowCL (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := lowCL4 μ ++ lowCL5 μ

/-- The weight-five truncation of `sin x₀ · x₂`. -/
def lowSL (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := lowSL4 μ ++ lowSL5 μ

/-- The weight-five truncation of `x₂²`. -/
def lowQL (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := lowQL4 μ ++ lowQL5 μ

/-- The weight-five part of `C₄(u) − 1`. -/
def lowF2 (l0 a2 a3 a4 : ℝ) : ℝ :=
  -(l0 ^ 2 + 2 * l0 * a2 + 2 * l0 * a3 + 2 * l0 * a4 + a2 ^ 2 + 2 * a2 * a3) / 2 +
    (l0 ^ 4 + 4 * l0 ^ 3 * a2) / 24

/-- The weight-five part of `S₅(u) − u`. -/
def lowF3 (l0 a2 a3 : ℝ) : ℝ :=
  -(l0 ^ 3 + 3 * l0 ^ 2 * a2 + 3 * l0 ^ 2 * a3 + 3 * l0 * a2 ^ 2) / 6 + l0 ^ 5 / 120

/-- The weight-five part of `(C₄(u) − 1) x` in the pieces of `u` and `x`. -/
def lowFC (l0 a2 a3 l2 c2 c3 : ℝ) : ℝ :=
  -((l0 ^ 2 + 2 * l0 * a2 + 2 * l0 * a3 + a2 ^ 2) * l2 + (l0 ^ 2 + 2 * l0 * a2) * c2 +
    l0 ^ 2 * c3) / 2 + l0 ^ 4 * l2 / 24

/-- The weight-five part of `S₅(u) x` in the pieces of `u` and `x`. -/
def lowFS (l0 a2 a3 a4 l2 c2 c3 c4 : ℝ) : ℝ :=
  (l0 * l2 + l0 * c2 + a2 * l2 + l0 * c3 + a2 * c2 + a3 * l2 + l0 * c4 + a2 * c3 + a3 * c2 +
    a4 * l2) - ((l0 ^ 3 + 3 * l0 ^ 2 * a2) * l2 + l0 ^ 3 * c2) / 6

/-- The weight-five part of `x²` in the pieces of `x`. -/
def lowFQ (l2 c2 c3 c4 : ℝ) : ℝ :=
  l2 ^ 2 + 2 * l2 * c2 + 2 * l2 * c3 + 2 * l2 * c4 + c2 ^ 2 + 2 * c2 * c3

/-- The weight-five truncation of `cos x₀ − 1` in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem low2_eq (μ : ℝ) (y : State 2) :
    lowF2 (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y) (pv (aL4 μ) y) = pv (low2L μ) y := by
  simp only [lowF2, lin0, pv, aL2, aL3, aL4, low2L, low2L4, low2L5, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `sin x₀ − x₀` in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem low3_eq (μ : ℝ) (y : State 2) :
    lowF3 (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y) = pv (low3L μ) y := by
  simp only [lowF3, lin0, pv, aL2, aL3, low3L, low3L4, low3L5, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `(cos x₀ − 1) x₂` in the monomials of `y`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem lowC_eq (μ : ℝ) (y : State 2) :
    lowFC (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y) (lin2 y) (pv (cL2 μ) y) (pv (cL3 μ) y) =
      pv (lowCL μ) y := by
  simp only [lowFC, lin0, lin2, pv, aL2, aL3, cL2, cL3, lowCL, lowCL4, lowCL5, poly3_cons,
    poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `sin x₀ · x₂` in the monomials of `y`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem lowS_eq (μ : ℝ) (y : State 2) :
    lowFS (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y) (pv (aL4 μ) y) (lin2 y) (pv (cL2 μ) y)
      (pv (cL3 μ) y) (pv (cL4 μ) y) = pv (lowSL μ) y := by
  simp only [lowFS, lin0, lin2, pv, aL2, aL3, aL4, cL2, cL3, cL4, lowSL, lowSL4, lowSL5,
    poly3_cons, poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The weight-five truncation of `x₂²` in the monomials of `y`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem lowQ_eq (μ : ℝ) (y : State 2) :
    lowFQ (lin2 y) (pv (cL2 μ) y) (pv (cL3 μ) y) (pv (cL4 μ) y) = pv (lowQL μ) y := by
  simp only [lowFQ, lin2, pv, cL2, cL3, cL4, lowQL, lowQL4, lowQL5, poly3_cons, poly3_nil,
    List.cons_append, List.nil_append]
  ring

/-- The Taylor polynomial of `cos x₀ − 1` minus its weight-five part is `O(‖y‖⁶)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem split2_isBigO (μ : ℝ) :
    (fun y : State 2 => 1 - tv μ y ^ 2 / 2 + tv μ y ^ 4 / 24 - 1 - lowF2 (lin0 y) (pv (aL2 μ) y)
      (pv (aL3 μ) y) (pv (aL4 μ) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a2 μ) (o_a4 μ) (by
    norm_num)).const_mul_left (-1)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_r3 μ)
    (o_r3 μ) (by norm_num)).const_mul_left (-1 / 2))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 o_l0 o_l0 (by norm_num)) o_l0 (by norm_num)) (o_r3 μ) (by
    norm_num)).const_mul_left (1 / 6))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    o_l0 o_l0 (by norm_num)) (o_r μ) (by norm_num)) (o_r μ) (by norm_num)).const_mul_left (1 /
    4))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 o_l0 (o_r μ) (by norm_num)) (o_r
    μ) (by norm_num)) (o_r μ) (by norm_num)).const_mul_left (1 / 6))).add ((Dynamics.isBigO_mul_pow
    (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow
    (k := 4) tendsto_norm0 (o_r μ) (o_r μ) (by norm_num)) (o_r μ) (by norm_num)) (o_r μ) (by
    norm_num)).const_mul_left (1 / 24))).congr_left fun y => ?_
  simp only [tv, lowF2]
  ring

/-- The Taylor polynomial of `sin x₀ − x₀` minus its weight-five part is `O(‖y‖⁶)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem split3_isBigO (μ : ℝ) :
    (fun y : State 2 => tv μ y - tv μ y ^ 3 / 6 + tv μ y ^ 5 / 120 - tv μ y -
      lowF3 (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 o_l0 o_l0 (by norm_num)) (o_a4 μ) (by norm_num)).const_mul_left (-1 / 2)).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_l0 (o_a2 μ) (by norm_num)) (o_a3 μ) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_l0 (o_a2 μ) (by norm_num)) (o_a4 μ) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    o_l0 (o_r3 μ) (by norm_num)) (o_r3 μ) (by norm_num)).const_mul_left (-1 / 2))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (o_r μ) (o_r μ) (by norm_num)) (o_r μ) (by norm_num)).const_mul_left (-1 / 6))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r μ) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) (o_u μ) (by
    norm_num)).const_mul_left (1 / 120))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r μ) (o_u μ) (by norm_num)) (o_u μ) (by
    norm_num)) (o_u μ) (by norm_num)) o_l0 (by norm_num)).const_mul_left (1 / 120))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r μ) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) o_l0 (by norm_num)) o_l0 (by
    norm_num)).const_mul_left (1 / 120))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r μ) (o_u μ) (by norm_num)) o_l0 (by
    norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)).const_mul_left (1 / 120))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r μ) o_l0 (by norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)) o_l0 (by
    norm_num)).const_mul_left (1 / 120))).congr_left fun y => ?_
  simp only [tv, lowF3]
  ring

/-- The Taylor polynomial of `(cos x₀ − 1) x₂` minus its weight-five part is `O(‖y‖⁶)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem splitC_isBigO (μ : ℝ) :
    (fun y : State 2 => (1 - tv μ y ^ 2 / 2 + tv μ y ^ 4 / 24 - 1) * x2v μ y -
      lowFC (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y) (lin2 y) (pv (cL2 μ) y) (pv (cL3 μ) y))
      =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine ((((((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k :=
    5) tendsto_norm0 o_l0 (o_a4 μ) (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (-1)).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (o_a2 μ) (o_a3 μ) (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (o_a2 μ) (o_a4 μ) (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (o_r3 μ) (o_r3 μ) (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (-1 / 2))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    o_l0 o_l0 (by norm_num)) (o_c4 μ) (by norm_num)).const_mul_left (-1 / 2))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_l0 (o_a2 μ) (by norm_num)) (o_C3 μ) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    o_l0 (o_a3 μ) (by norm_num)) (o_C μ) (by norm_num)).const_mul_left (-1))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (o_a2 μ) (o_a2 μ) (by norm_num)) (o_C μ) (by norm_num)).const_mul_left (-1 / 2))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r μ) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) (o_X μ) (by
    norm_num)).const_mul_left (1 / 24))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r μ) (o_u μ) (by norm_num)) (o_u μ) (by
    norm_num)) o_l0 (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (1 / 24))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (o_r μ) (o_u μ) (by norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)) (o_X μ) (by
    norm_num)).const_mul_left (1 / 24))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (o_r μ) o_l0 (by norm_num)) o_l0 (by norm_num))
    o_l0 (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (1 / 24))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    o_l0 o_l0 (by norm_num)) o_l0 (by norm_num)) o_l0 (by norm_num)) (o_C μ) (by
    norm_num)).const_mul_left (1 / 24))).congr_left fun y => ?_
  simp only [tv, x2v, lowFC]
  ring

/-- The Taylor polynomial of `sin x₀ · x₂` minus its weight-five part is `O(‖y‖⁶)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem splitS_isBigO (μ : ℝ) :
    (fun y : State 2 => (tv μ y - tv μ y ^ 3 / 6 + tv μ y ^ 5 / 120) * x2v μ y -
      lowFS (lin0 y) (pv (aL2 μ) y) (pv (aL3 μ) y) (pv (aL4 μ) y) (lin2 y) (pv (cL2 μ) y)
        (pv (cL3 μ) y) (pv (cL4 μ) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine ((((((((((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a2 μ) (o_c4 μ) (by
    norm_num)).const_mul_left (1)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_a3 μ)
    (o_C3 μ) (by norm_num)).const_mul_left (1))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (o_a4 μ) (o_C μ) (by norm_num)).const_mul_left (1))).add ((Dynamics.isBigO_mul_pow
    (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow
    (k := 2) tendsto_norm0 o_l0 o_l0 (by norm_num)) (o_r3 μ) (by norm_num)) (o_X μ) (by
    norm_num)).const_mul_left (-1 / 2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    o_l0 (o_r μ) (by norm_num)) (o_r μ) (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (-1 /
    2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (o_r μ) (o_r μ) (by norm_num))
    (o_r μ) (by norm_num)) (o_X μ) (by norm_num)).const_mul_left (-1 / 6))).add
    ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0 o_l0 o_l0 (by norm_num)) o_l0 (by norm_num))
    (o_C3 μ) (by norm_num)).const_mul_left (-1 / 6))).add ((Dynamics.isBigO_mul_pow (k := 6)
    tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2)
    tendsto_norm0 o_l0 o_l0 (by norm_num)) (o_a2 μ) (by norm_num)) (o_C μ) (by
    norm_num)).const_mul_left (-1 / 2))).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 5) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 4) tendsto_norm0
    (Dynamics.isBigO_mul_pow (k := 3) tendsto_norm0 (Dynamics.isBigO_mul_pow (k := 2) tendsto_norm0
    (o_u μ) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) (o_u μ) (by norm_num)) (o_u μ) (by
    norm_num)) (o_X μ) (by norm_num)).const_mul_left (1 / 120))).congr_left fun y => ?_
  simp only [tv, x2v, lowFS]
  ring

/-- `x₂²` minus its weight-five part is `O(‖y‖⁶)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem splitQ_isBigO (μ : ℝ) :
    (fun y : State 2 => x2v μ y * x2v μ y - lowFQ (lin2 y) (pv (cL2 μ) y) (pv (cL3 μ) y)
      (pv (cL4 μ) y)) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_c2 μ) (o_c4 μ) (by
    norm_num)).const_mul_left (2)).add ((Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 (o_C3 μ)
    (o_C3 μ) (by norm_num)).const_mul_left (1))).congr_left fun y => ?_
  simp only [x2v, lowFQ]
  ring

@[tmio M, powerlib_domain] private theorem tv_isBigO (μ : ℝ) :
    (fun y => tv μ y) =O[𝓝 0] fun y => ‖y‖ :=
  (o_u μ).congr_right fun _ => pow_one _

@[tmio M, powerlib_domain] private theorem tv_tendsto (μ : ℝ) :
    Tendsto (fun y => tv μ y) (𝓝 0) (𝓝 0) :=
  (tv_isBigO μ).trans_tendsto tendsto_norm0

/-- **`cos x₀ − 1` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem f2_sub_low (μ : ℝ) :
    (fun y => Real.cos (tv μ y) - 1 - pv (low2L μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hc := Dynamics.isBigO_comp_pow Dynamics.cos_sub_taylor_isBigO (tv_tendsto μ) (tv_isBigO μ)
  refine (hc.add (split2_isBigO μ)).congr_left fun y => ?_
  simp only [← low2_eq μ y]
  ring

/-- **`sin x₀ − x₀` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem f3_sub_low (μ : ℝ) :
    (fun y => Real.sin (tv μ y) - tv μ y - pv (low3L μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hn := Dynamics.isBigO_comp_pow Dynamics.sin_sub_taylor5_isBigO (tv_tendsto μ)
    (tv_isBigO μ)
  refine (hn.add (split3_isBigO μ)).congr_left fun y => ?_
  simp only [← low3_eq μ y]
  ring

/-- **`(cos x₀ − 1) x₂` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem fC_sub_low (μ : ℝ) :
    (fun y => (Real.cos (tv μ y) - 1) * x2v μ y - pv (lowCL μ) y) =O[𝓝 0]
      fun y => ‖y‖ ^ 6 := by
  have hc := Dynamics.isBigO_comp_pow Dynamics.cos_sub_taylor_isBigO (tv_tendsto μ) (tv_isBigO μ)
  have h1 := Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 hc (o_X μ) (by norm_num)
  refine (h1.add (splitC_isBigO μ)).congr_left fun y => ?_
  simp only [← lowC_eq μ y]
  ring

/-- **`sin x₀ · x₂` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem fS_sub_low (μ : ℝ) :
    (fun y => Real.sin (tv μ y) * x2v μ y - pv (lowSL μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have hn := Dynamics.isBigO_comp_pow Dynamics.sin_sub_taylor5_isBigO (tv_tendsto μ)
    (tv_isBigO μ)
  have h1 := Dynamics.isBigO_mul_pow (k := 6) tendsto_norm0 hn (o_X μ) (by norm_num)
  refine (h1.add (splitS_isBigO μ)).congr_left fun y => ?_
  simp only [← lowS_eq μ y]
  ring

/-- **`x₂²` on the manifold minus its weight-five truncation is `O(‖y‖⁶)`.** Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem fQ_sub_low (μ : ℝ) :
    (fun y => x2v μ y * x2v μ y - pv (lowQL μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 :=
  (splitQ_isBigO μ).congr_left fun y => by rw [lowQ_eq]

/-! ## The quintic jet of the chart field -/

/-- The truncated active-power nonlinearity. -/
def F1low (μ : ℝ) (y : State 2) : ℝ :=
  -(122 / 85) * ((2 * μ + 5 * μ ^ 2) / 10 * pv (lowQL μ) y - pv (low2L μ) y +
    1 / 2 * pv (low3L μ) y + μ * pv (lowCL μ) y - μ / 2 * pv (lowSL μ) y)

/-- The truncated reactive-power nonlinearity. -/
def F2low (μ : ℝ) (y : State 2) : ℝ :=
  (2 * μ + 5 * μ ^ 2) / 20 * pv (lowQL μ) y - 1 / 2 * pv (low2L μ) y - pv (low3L μ) y +
    μ / 2 * pv (lowCL μ) y + μ * pv (lowSL μ) y

/-- `F₁ − F₁ˡᵒʷ = O(‖y‖⁶)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem F1_sub_low (μ : ℝ) :
    (fun y => F1v μ y - F1low μ y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have h := (((((fQ_sub_low μ).const_mul_left ((2 * μ + 5 * μ ^ 2) / 10)).sub
    (f2_sub_low μ)).add ((f3_sub_low μ).const_mul_left (1 / 2))).add
    ((fC_sub_low μ).const_mul_left μ)).sub ((fS_sub_low μ).const_mul_left (μ / 2))
  refine (h.const_mul_left (-(122 / 85))).congr_left fun y => ?_
  simp only [F1v, F1low]
  ring

/-- `F₂ − F₂ˡᵒʷ = O(‖y‖⁶)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem F2_sub_low (μ : ℝ) :
    (fun y => F2v μ y - F2low μ y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have h := ((((fQ_sub_low μ).const_mul_left ((2 * μ + 5 * μ ^ 2) / 20)).sub
    ((f2_sub_low μ).const_mul_left (1 / 2))).sub (f3_sub_low μ)).add
    (((fC_sub_low μ).const_mul_left (μ / 2)).add ((fS_sub_low μ).const_mul_left μ))
  refine h.congr_left fun y => ?_
  simp only [F2v, F2low]
  ring

/-- The jet of the first chart coordinate. -/
def cF (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := cF2 μ ++ cF3 μ ++ cF4 μ ++ cF5 μ

/-- The jet of the second chart coordinate. -/
def cG (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := cG2 μ ++ cG3 μ ++ cG4 μ ++ cG5 μ

/-- The jet of the first chart coordinate from the truncated nonlinearities. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem cF_eq (μ : ℝ) (y : State 2) :
    pv (cF μ) y = 3145 / 44218 * F1low μ y - 1626 / 22109 * F2low μ y := by
  simp only [F1low, F2low, pv, cF, cF2, cF3, cF4, cF5, low2L, low2L4, low2L5, low3L, low3L4,
    low3L5, lowCL, lowCL4, lowCL5, lowSL, lowSL4, lowSL5, lowQL, lowQL4, lowQL5, poly3_cons,
    poly3_nil, List.cons_append, List.nil_append]
  ring

/-- The jet of the second chart coordinate from the truncated nonlinearities. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem cG_eq (μ : ℝ) (y : State 2) :
    pv (cG μ) y = -17595 / 44218 * F1low μ y - 2854 / 22109 * F2low μ y := by
  simp only [F1low, F2low, pv, cG, cG2, cG3, cG4, cG5, low2L, low2L4, low2L5, low3L, low3L4,
    low3L5, lowCL, lowCL4, lowCL5, lowSL, lowSL4, lowSL5, lowQL, lowQL4, lowQL5, poly3_cons,
    poly3_nil, List.cons_append, List.nil_append]
  ring

/-- **The first chart coordinate has the jet `cF`**: `G₀ − cF = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G0_sub_jet (hμ : 0 < μ) :
    (fun y => G0 μ y - pv (cF μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((F1_sub_low μ).const_mul_left (3145 / 44218)).sub
    ((F2_sub_low μ).const_mul_left (1626 / 22109))).congr_left fun y => ?_
  rw [(G_eq hμ y).1, cF_eq]
  ring

/-- **The second chart coordinate has the jet `cG`**: `G₁ − cG = O(‖y‖⁶)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem G1_sub_jet (hμ : 0 < μ) :
    (fun y => G1 μ y - pv (cG μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  refine (((F1_sub_low μ).const_mul_left (-17595 / 44218)).sub
    ((F2_sub_low μ).const_mul_left (2854 / 22109))).congr_left fun y => ?_
  rw [(G_eq hμ y).2, cG_eq]
  ring

/-- The tails of the jet: `G − J₃ = O(‖y‖⁴)` and `G − J₄ = O(‖y‖⁵)` in both coordinates. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_tail_bounds (hμ : 0 < μ) :
    ((fun y => G0 μ y - pv (cF2 μ ++ cF3 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 4) ∧
      ((fun y => G1 μ y - pv (cG2 μ ++ cG3 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 4) ∧
      ((fun y => G0 μ y - pv (cF2 μ ++ cF3 μ ++ cF4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 5) ∧
      ((fun y => G1 μ y - pv (cG2 μ ++ cG3 μ ++ cG4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 5) := by
  have hF4 : (fun y : State 2 => pv (cF4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
    pv_isBigO _ (by simp [cF4])
  have hF5 : (fun y : State 2 => pv (cF5 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [cF5])
  have hG4 : (fun y : State 2 => pv (cG4 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 4 :=
    pv_isBigO _ (by simp [cG4])
  have hG5 : (fun y : State 2 => pv (cG5 μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [cG5])
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((mono (G0_sub_jet hμ) (by norm_num)).add
      (hF4.add (mono hF5 (by norm_num)))).congr_left fun y => ?_
    simp only [cF, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono (G1_sub_jet hμ) (by norm_num)).add
      (hG4.add (mono hG5 (by norm_num)))).congr_left fun y => ?_
    simp only [cG, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono (G0_sub_jet hμ) (by norm_num)).add hF5).congr_left fun y => ?_
    simp only [cF, PlanarFocus.Jet5.poly3_append, pv]; ring
  · refine ((mono (G1_sub_jet hμ) (by norm_num)).add hG5).congr_left fun y => ?_
    simp only [cG, PlanarFocus.Jet5.poly3_append, pv]; ring

/-! ## The invariance defect -/

/-- The truncated active-power nonlinearity, degrees two to four. -/
def F1low4 (μ : ℝ) (y : State 2) : ℝ :=
  -(122 / 85) * ((2 * μ + 5 * μ ^ 2) / 10 * pv (lowQL4 μ) y - pv (low2L4 μ) y +
    1 / 2 * pv (low3L4 μ) y + μ * pv (lowCL4 μ) y - μ / 2 * pv (lowSL4 μ) y)

/-- `F₁ − F₁ˡᵒʷ⁴ = O(‖y‖⁵)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem F1_sub_low4 (μ : ℝ) :
    (fun y => F1v μ y - F1low4 μ y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := by
  have h5 : (fun y : State 2 => -(122 / 85) * ((2 * μ + 5 * μ ^ 2) / 10 * pv (lowQL5 μ) y -
      pv (low2L5 μ) y + 1 / 2 * pv (low3L5 μ) y + μ * pv (lowCL5 μ) y -
        μ / 2 * pv (lowSL5 μ) y)) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (((((((pv_isBigO (lowQL5 μ) (by simp [lowQL5])).const_mul_left
      ((2 * μ + 5 * μ ^ 2) / 10)).sub (pv_isBigO (low2L5 μ) (by simp [low2L5]))).add
      ((pv_isBigO (low3L5 μ) (by simp [low3L5])).const_mul_left (1 / 2))).add
      ((pv_isBigO (lowCL5 μ) (by simp [lowCL5])).const_mul_left μ)).sub
      ((pv_isBigO (lowSL5 μ) (by simp [lowSL5])).const_mul_left (μ / 2))).const_mul_left
      (-(122 / 85)))
  refine ((mono (F1_sub_low μ) (by norm_num)).add h5).congr_left fun y => ?_
  simp only [F1low, F1low4, low2L, low3L, lowCL, lowSL, lowQL, pv, PlanarFocus.Jet5.poly3_append]
  ring

/-- The `w`-component of the invariance defect over `y`. -/
def dcomp (μ : ℝ) (y : State 2) : ℝ :=
  dpoly3 (hL μ) (y 0) (y 1) 0 (-y 1 + G0 μ y) (y 0 + G1 μ y) 0 + 122 / 85 * pv (hL μ) y -
    (F1v μ y - (1 / 5 * G0 μ y - 11 / 5 * G1 μ y))

/-- **The homological equations make the polynomial part of the defect of degree at least five**
(`highD` has degrees five to eight), for every `μ`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem main_eq_high (μ : ℝ) (y : State 2) :
    dpoly3 (hL μ) (y 0) (y 1) 0 (-y 1 + pv (cF2 μ ++ cF3 μ) y) (y 0 + pv (cG2 μ ++ cG3 μ) y) 0 +
      122 / 85 * pv (hL μ) y - (F1low4 μ y - (1 / 5 * pv (cF2 μ ++ cF3 μ ++ cF4 μ) y -
        11 / 5 * pv (cG2 μ ++ cG3 μ ++ cG4 μ) y)) = pv (highD μ) y := by
  simp only [dpoly3_cons, dpoly3_nil, poly3_cons, poly3_nil, hL, hL2, hL3, hL4, cF2, cF3, cF4,
    cG2, cG3, cG4, F1low4, lowQL4, low2L4, low3L4, lowCL4, lowSL4, highD, pv, List.cons_append,
    List.nil_append]
  ring

/-- **The invariance defect at a chart point** is `d(y) w`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem defect_eq (hμ : 0 < μ) (y : State 2) :
    invarianceDefect (fderiv ℝ (bpath μ).field 0) (critP qC pC) (fnl μ) (manifold μ)
      (critι qC y) = dcomp μ y • wsv := by
  have hc := isCritical_C hμ
  obtain ⟨L, hL', hLv⟩ := hasFDerivAt_manifoldH μ y
  have hdef := invarianceDefect_comp_chart (A := fderiv ℝ (bpath μ).field 0) (f := fnl μ)
    hc.isChart hL'.differentiableAt
  rw [show (fun x => manifoldH μ (critπ pC x)) = manifold μ from rfl, hL'.fderiv] at hdef
  rw [hdef, chartField_eq hμ, hLv]
  have hφ : manifold μ (critι qC y) = manifoldH μ y := by rw [manifold, hc.critπ_critι]
  have hN : normalField (fderiv ℝ (bpath μ).field 0) (critP qC pC) (fnl μ) (manifold μ)
      (critι qC y) = (-(122 / 85) * pv (hL μ) y +
        (F1v μ y - (1 / 5 * G0 μ y - 11 / 5 * G1 μ y))) • wsv := by
    rw [normalField, hφ]
    simp only [_root_.sub_apply, one_apply_eq_self, critP, ContinuousLinearMap.comp_apply]
    have hA : fderiv ℝ (bpath μ).field 0 (manifoldH μ y) = (-(122 / 85) * pv (hL μ) y) • wsv := by
      rw [manifoldH, map_smul, A_wsv hμ, smul_smul, pv]; ring_nf
    rw [hA, map_smul, critπ_wsv, smul_zero, map_zero, sub_zero, show critι qC y + manifoldH μ y =
      chartPt μ y from rfl, sub_critP, (fnl_chartPt hμ y).2.1, add_smul]
    rfl
  rw [hN, ← sub_smul]
  congr 1
  simp only [PiLp.add_apply, rotL_apply0, rotL_apply1, dcomp, G0, G1, pv]
  ring_nf

/-- The `w`-component of the defect is `O(‖y‖⁵)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dcomp_isBigO (hμ : 0 < μ) :
    (fun y => dcomp μ y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := by
  have e : ∀ y, dcomp μ y = pv (highD μ) y +
      (poly3 ((hL μ).map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0 *
          (G0 μ y - pv (cF2 μ ++ cF3 μ) y) +
        poly3 ((hL μ).map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0 *
          (G1 μ y - pv (cG2 μ ++ cG3 μ) y)) - (F1v μ y - F1low4 μ y) +
      (1 / 5 * (G0 μ y - pv (cF2 μ ++ cF3 μ ++ cF4 μ) y) -
        11 / 5 * (G1 μ y - pv (cG2 μ ++ cG3 μ ++ cG4 μ) y)) := by
    intro y
    rw [← main_eq_high μ y, dcomp, Dynamics.Degenerate.dpoly3_eq_partials,
      Dynamics.Degenerate.dpoly3_eq_partials]
    ring
  obtain ⟨hG0_3, hG1_3, hG0_4, hG1_4⟩ := jet_tail_bounds hμ
  have hdx : (fun y : State 2 => poly3 ((hL μ).map Dynamics.Degenerate.dxTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [hL, hL2, hL3, hL4, Dynamics.Degenerate.dxTerm])
  have hdy : (fun y : State 2 => poly3 ((hL μ).map Dynamics.Degenerate.dyTerm) (y 0) (y 1) 0)
      =O[𝓝 0] fun y => ‖y‖ ^ 1 :=
    pv_isBigO _ (by simp [hL, hL2, hL3, hL4, Dynamics.Degenerate.dyTerm])
  have hhigh : (fun y : State 2 => pv (highD μ) y) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    pv_isBigO _ (by simp [highD])
  refine (((hhigh.add ((Dynamics.isBigO_mul_pow tendsto_norm0 hdx hG0_3 (by norm_num)).add
    (Dynamics.isBigO_mul_pow tendsto_norm0 hdy hG1_3 (by norm_num)))).sub (F1_sub_low4 μ)).add
      ((hG0_4.const_mul_left (1 / 5)).sub (hG1_4.const_mul_left (11 / 5)))).congr_left
      fun y => ?_
  rw [e y]

/-- **The invariance defect is `O(‖u‖⁵)` on the centre subspace.** Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem isOrder_defect (hμ : 0 < μ) :
    IsOrder (critP qC pC) (invarianceDefect (fderiv ℝ (bpath μ).field 0) (critP qC pC) (fnl μ)
      (manifold μ)) 5 := by
  have h := (isCritical_C hμ).isChart.isOrder_of_isBigO (k := 5)
    (G := invarianceDefect (fderiv ℝ (bpath μ).field 0) (critP qC pC) (fnl μ) (manifold μ)) ?_
  · exact_mod_cast h
  have h2 : (fun y : State 2 => dcomp μ y • wsv) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (IsBigO.of_bound ‖wsv‖ (Eventually.of_forall fun y => by
      rw [norm_smul, mul_comm])).trans (dcomp_isBigO hμ)
  exact h2.congr_left fun y => (defect_eq hμ y).symm

/-! ## The jet and the Lyapunov coefficients along the path -/

/-- **The quintic jet** of the chart field (rotation coordinates of `rotL 1`). -/
def jet (μ : ℝ) : Jet5 where
  a20 := (-37147 / 110545 + 961 / 44218 * μ - 1535 / 22109 * μ ^ 2)
  a11 := (-6754 / 110545 - 34 / 22109 * μ - 3070 / 22109 * μ ^ 2)
  a02 := (-307 / 110545 - 1029 / 44218 * μ - 1535 / 22109 * μ ^ 2)
  b20 := (27104 / 22109 + 44817 / 44218 * μ + 5600 / 22109 * μ ^ 2)
  b11 := (4928 / 22109 + 26482 / 22109 * μ + 11200 / 22109 * μ ^ 2)
  b02 := (224 / 22109 + 8147 / 44218 * μ + 5600 / 22109 * μ ^ 2)
  a30 := (-85191236974723 / 802573659813900 - 129604009223567 / 428039285234080 * μ + 4831751266461
    / 42803928523408 * μ ^ 2 - 3617963686185 / 85607857046816 * μ ^ 3 + 472798212775 /
    21401964261704 * μ ^ 4)
  a21 := (-19479179631393 / 267524553271300 - 124369452344171 / 428039285234080 * μ + 8360095501013
    / 42803928523408 * μ ^ 2 - 10047891863605 / 85607857046816 * μ ^ 3 + 1083554036325 /
    21401964261704 * μ ^ 4)
  a12 := (-12276562850863 / 267524553271300 + 7557661958409 / 428039285234080 * μ + 4832472952093 /
    42803928523408 * μ ^ 2 - 10359724221905 / 85607857046816 * μ ^ 3 + 1934607233075 /
    21401964261704 * μ ^ 4)
  a03 := (-2929204075133 / 802573659813900 + 13237912723513 / 428039285234080 * μ + 2246724615041 /
    42803928523408 * μ ^ 2 - 2392383236985 / 85607857046816 * μ ^ 3 + 1323851409525 / 21401964261704
    * μ ^ 4)
  b30 := (-396715552556389 / 802573659813900 + 88002303300989 / 428039285234080 * μ - 336190057733 /
    3292609886416 * μ ^ 2 - 93074088205 / 85607857046816 * μ ^ 3 - 215608305500 / 2675245532713 * μ
    ^ 4)
  b21 := (6744931303601 / 267524553271300 + 135746952759777 / 428039285234080 * μ - 406659690369 /
    3292609886416 * μ ^ 2 + 19724911389335 / 85607857046816 * μ ^ 3 - 494128876500 / 2675245532713 *
    μ ^ 4)
  b12 := (38940262672691 / 267524553271300 - 253145568550763 / 428039285234080 * μ - 163812127789 /
    3292609886416 * μ ^ 2 + 884379837035 / 85607857046816 * μ ^ 3 - 882231311500 / 2675245532713 * μ
    ^ 4)
  b03 := (10154783669881 / 802573659813900 - 44137599091051 / 428039285234080 * μ - 652552437653 /
    3292609886416 * μ ^ 2 + 9396508756995 / 85607857046816 * μ ^ 3 - 603710740500 / 2675245532713 *
    μ ^ 4)
  a40 := (823436812702714734162492208 / 9700299845187169371708813375 + 16881074459580595055230362151
    / 124163838018395767957872811200 * μ - 1770080725530035691199200199 /
    33110356804905538122099416320 * μ ^ 2 + 134297858879227266199862207 /
    827758920122638453052485408 * μ ^ 3 - 64917077543216057968268375 / 3311035680490553812209941632
    * μ ^ 4 + 34638125685898769942541925 / 1655517840245276906104970816 * μ ^ 5 +
    27906053495228904004773125 / 6622071360981107624419883264 * μ ^ 6)
  a31 := (77380210714600362232745723 / 38801199380748677486835253500 + 1158659907399019365814108561
    / 31040959504598941989468202800 * μ + 90244813814093925323111201 / 8277589201226384530524854080
    * μ ^ 2 + 82957226619537279337142167 / 206939730030659613263121352 * μ ^ 3 -
    95660993891002416837390075 / 827758920122638453052485408 * μ ^ 4 + 22509503817643637444053925 /
    413879460061319226526242704 * μ ^ 5 - 50442481441125408022116875 / 1655517840245276906104970816
    * μ ^ 6)
  a22 := (-709524457210478614241056207 / 25867466253832451657890169000 + 848791770025574462977130221
    / 20693973003065961326312135200 * μ + 700726255377077785229555653 /
    16555178402452769061049708160 * μ ^ 2 + 355204394077508437033950487 /
    827758920122638453052485408 * μ ^ 3 - 371816456187496989576195075 / 1655517840245276906104970816
    * μ ^ 4 + 1579599850882288359159325 / 25867466253832451657890169 * μ ^ 5 -
    177561355366230471777314375 / 3311035680490553812209941632 * μ ^ 6)
  a13 := (-174442322099939716647259303 / 9700299845187169371708813375 - 1325798290001257887322483369
    / 31040959504598941989468202800 * μ + 24507019398221773991104411 / 201892419542106939768898880 *
    μ ^ 2 + 54324552753936223213468399 / 413879460061319226526242704 * μ ^ 3 -
    118715367143939274882270725 / 827758920122638453052485408 * μ ^ 4 + 15579965233535448428533025 /
    206939730030659613263121352 * μ ^ 5 - 141962485328883657409690625 / 1655517840245276906104970816
    * μ ^ 6)
  a04 := (-181479831399191806936855771 / 77602398761497354973670507000 - 315577847355522374736095209
    / 124163838018395767957872811200 * μ + 1046259788858299223031499601 /
    33110356804905538122099416320 * μ ^ 2 + 4277498705378437886408261 / 413879460061319226526242704
    * μ ^ 3 - 300155478551091668087622175 / 3311035680490553812209941632 * μ ^ 4 +
    28589789116567074340491175 / 1655517840245276906104970816 * μ ^ 5 - 515614643614675422779561875
    / 6622071360981107624419883264 * μ ^ 6)
  b40 := (-17700966336966663076383785063 / 31040959504598941989468202800 -
    464395918496858610570980533633 / 248327676036791535915745622400 * μ -
    989741040942050161557659039 / 2069397300306596132631213520 * μ ^ 2 - 565405447022867382421426091
    / 827758920122638453052485408 * μ ^ 3 - 13997172048193238214289465 / 827758920122638453052485408
    * μ ^ 4 - 401492432326002090415897725 / 3311035680490553812209941632 * μ ^ 5 -
    3181471896850200782303125 / 206939730030659613263121352 * μ ^ 6)
  b31 := (-532798447677442040483856892 / 1940059969037433874341762675 -
    98540278133561969504753020393 / 62081919009197883978936405600 * μ - 2503161861674323520271397041
    / 2069397300306596132631213520 * μ ^ 2 - 202193909121721609353531561 /
    206939730030659613263121352 * μ ^ 3 + 132887090065634594254561995 / 413879460061319226526242704
    * μ ^ 4 + 15651995073182531931891275 / 827758920122638453052485408 * μ ^ 5 +
    5750771499802570947146875 / 51734932507664903315780338 * μ ^ 6)
  b22 := (-63871475308231838875823556 / 646686656345811291447254225 - 28112623615856562917907522303
    / 41387946006131922652624270400 * μ - 756903372749449276857244207 / 1034698650153298066315606760
    * μ ^ 2 - 1251788369537412290283482061 / 827758920122638453052485408 * μ ^ 3 +
    20436782228946079806910430 / 25867466253832451657890169 * μ ^ 4 - 306904802258201822609131675 /
    1655517840245276906104970816 * μ ^ 5 + 20243151263251030984384375 / 103469865015329806631560676
    * μ ^ 6)
  b13 := (273938176984114843493050547 / 7760239876149735497367050700 - 6708092148221976140474027363
    / 62081919009197883978936405600 * μ - 1101059856785721027739662861 /
    2069397300306596132631213520 * μ ^ 2 - 62617652594715836387962377 / 413879460061319226526242704
    * μ ^ 3 + 174984169740170368399833845 / 413879460061319226526242704 * μ ^ 4 +
    126834336217667240684171775 / 827758920122638453052485408 * μ ^ 5 + 16184648164530710128140625 /
    51734932507664903315780338 * μ ^ 6)
  b04 := (224635026198666323568252667 / 31040959504598941989468202800 - 5807293336092854947981006073
    / 248327676036791535915745622400 * μ - 129926053301793903857131199 /
    2069397300306596132631213520 * μ ^ 2 - 6277099198106050237427131 / 51734932507664903315780338 *
    μ ^ 3 + 309422484496587096371509885 / 827758920122638453052485408 * μ ^ 4 -
    312190055010597553245524225 / 3311035680490553812209941632 * μ ^ 5 + 58783428425125862531871875
    / 206939730030659613263121352 * μ ^ 6)
  a50 := (3026237970397718632812936502951838241356917 / 61262816562629575630613522982505764355800000
    + 1548334410630804383726894348211039892042631 / 4901025325010366050449081838600461148464000 * μ
    + 566145472262208434958661412745374196981251 / 15683281040033171361437061883521475675084800 * μ
    ^ 2 - 24983268985039209211926060474951979950120617 /
    382672057376809381219064309957924006472069120 * μ ^ 3 +
    148185590354866064975333070462518295405673 / 6377867622946823020317738499298733441201152 * μ ^ 4
    - 27237550718417128721656440660838957379755 / 981210403530280464664267461430574375569408 * μ ^ 5
    + 631671893248779930071182118443140591753075 / 12755735245893646040635476998597466882402304 * μ
    ^ 6 + 277861338593978441603068988692772383909625 / 25511470491787292081270953997194933764804608
    * μ ^ 7 + 99137674610216550066274388868403576638125 /
    6377867622946823020317738499298733441201152 * μ ^ 8)
  a41 := (382307014253753788049369380989381219142847 / 12252563312525915126122704596501152871160000
    + 30760072850175383460499885499168640691153 / 98020506500207321008981636772009222969280 * μ +
    232293663734309501868728356197590276026769 / 3136656208006634272287412376704295135016960 * μ ^ 2
    - 21630190408573568745515797973419867168616459 / 76534411475361876243812861991584801294413824 *
    μ ^ 3 + 3035848875478307189544435939864887094578455 /
    19133602868840469060953215497896200323603456 * μ ^ 4 -
    2134153974107766498963179573594573908738225 / 12755735245893646040635476998597466882402304 * μ ^
    5 + 1327720436986608709903841447584946192324125 / 12755735245893646040635476998597466882402304 *
    μ ^ 6 + 104399590671169920065476731362284415354375 /
    25511470491787292081270953997194933764804608 * μ ^ 7 + 23338523033985584829022596942660664465625
    / 6377867622946823020317738499298733441201152 * μ ^ 8)
  a32 := (107392296812469042436146166102303862526227 / 6126281656262957563061352298250576435580000 +
    9012163468406678966555001556114397063657 / 40841877708419717087075681988337176237200 * μ -
    167223111817502837231153785833288545378293 / 1568328104003317136143706188352147567508480 * μ ^ 2
    - 6549751103585729860146513941745943392457151 / 38267205737680938121906430995792400647206912 * μ
    ^ 3 - 457800212535502924585599560824507972396285 / 9566801434420234530476607748948100161801728 *
    μ ^ 4 - 2232769642724763166667441935651148066338625 /
    6377867622946823020317738499298733441201152 * μ ^ 5 +
    1332350388810502040813249186011794001907875 / 6377867622946823020317738499298733441201152 * μ ^
    6 - 31102709048684120503898252665634763150625 / 981210403530280464664267461430574375569408 * μ ^
    7 + 198930065130918792505874312477260002396875 / 3188933811473411510158869249649366720600576 * μ
    ^ 8)
  a23 := (-31992125964606908326769057251903776467443 / 6126281656262957563061352298250576435580000 +
    6116209755325786666264788740406741728021 / 61262816562629575630613522982505764355800 * μ -
    50623862234000716991936012351797570795807 / 313665620800663427228741237670429513501696 * μ ^ 2 -
    10231956920916630816064793979680094601951393 / 38267205737680938121906430995792400647206912 * μ
    ^ 3 - 97602960705485078876841177879834234478375 / 3188933811473411510158869249649366720600576 *
    μ ^ 4 - 14897879055816021343345960262927067277975 / 37738861674241556333241056208868245214208 *
    μ ^ 5 + 2469651347813134835790647936838441247479125 /
    6377867622946823020317738499298733441201152 * μ ^ 6 + 167680956663031721465412096723679665798125
    / 12755735245893646040635476998597466882402304 * μ ^ 7 +
    292366536965648177313131795011446460109375 / 3188933811473411510158869249649366720600576 * μ ^
    8)
  a14 := (-79550998483331655686799939767471369080163 / 12252563312525915126122704596501152871160000
    + 1788532008097544214034377040022347602989 / 75400389615544093083832028286160940745600 * μ -
    185061760870594583881714762132419083852057 / 3136656208006634272287412376704295135016960 * μ ^ 2
    - 3816129571781921452779886807828451091012385 / 76534411475361876243812861991584801294413824 * μ
    ^ 3 - 3887533078376433552454174126065229486491565 / 19133602868840469060953215497896200323603456
    * μ ^ 4 - 1528555850807223321035391301711684427035675 /
    12755735245893646040635476998597466882402304 * μ ^ 5 +
    229732770769895929864187985499514234216375 / 981210403530280464664267461430574375569408 * μ ^ 6
    - 452465420181437656369210335848462822626875 / 25511470491787292081270953997194933764804608 * μ
    ^ 7 + 649591701847114872229479614154441896040625 / 6377867622946823020317738499298733441201152 *
    μ ^ 8)
  a05 := (-67873707351842217142538259625663415896433 / 61262816562629575630613522982505764355800000
    - 1546119870241465159257598078811417916429 / 816837554168394341741513639766743524744000 * μ -
    312961341009026107225217061194354355680459 / 15683281040033171361437061883521475675084800 * μ ^
    2 - 19683137283342189071236680345399422660582827 / 382672057376809381219064309957924006472069120
    * μ ^ 3 - 1464228290719562591276327709587109544525321 /
    19133602868840469060953215497896200323603456 * μ ^ 4 +
    114095907674914176403394661122564246169035 / 12755735245893646040635476998597466882402304 * μ ^
    5 + 2605056022139872505486366292878892246224325 / 12755735245893646040635476998597466882402304 *
    μ ^ 6 + 28315215865739083644071567751146006772375 / 1962420807060560929328534922861148751138816
    * μ ^ 7 + 775219757211351329246855799119109330288125 /
    6377867622946823020317738499298733441201152 * μ ^ 8)
  b50 := (-2707089247823137321265169806920186714589613 /
    20420938854209858543537840994168588118600000 - 379038121653422979621569002237936324526721 /
    408418777084197170870756819883371762372000 * μ - 490708656565937397214826039192616614007771 /
    5227760346677723787145687294507158558361600 * μ ^ 2 +
    36548380596064125192356332786438000142961523 / 382672057376809381219064309957924006472069120 * μ
    ^ 3 - 88005496209062402736988566768325562463723 / 1594466905736705755079434624824683360300288 *
    μ ^ 4 - 313846515829594800407513710611216514221855 / 981210403530280464664267461430574375569408
    * μ ^ 5 - 3242378207605810979548841431605478684215125 /
    12755735245893646040635476998597466882402304 * μ ^ 6 -
    4011977509189607521319755042153708151741875 / 25511470491787292081270953997194933764804608 * μ ^
    7 - 11302340753607750007555712085974349128125 / 199308363217088219384929328103085420037536 * μ ^
    8)
  b41 := (-784298098678520739970766097755367606085983 / 4084187770841971708707568198833717623720000
    - 1527266784900217842453144607248501261746491 / 980205065002073210089816367720092229692800 * μ -
    1155794289248699074533252020055413282351131 / 3136656208006634272287412376704295135016960 * μ ^
    2 + 37827105836724395926813046921219061752742435 / 25511470491787292081270953997194933764804608
    * μ ^ 3 - 1891209259489884624389593922105822188761655 /
    4783400717210117265238303874474050080900864 * μ ^ 4 +
    10224660799084244871279613907254023389263875 / 12755735245893646040635476998597466882402304 * μ
    ^ 5 - 5021083649050095637910593340472086999323875 / 12755735245893646040635476998597466882402304
    * μ ^ 6 + 2828827946131914646057454339800811428581875 /
    25511470491787292081270953997194933764804608 * μ ^ 7 - 2660743668369692081484660889228414515625
    / 199308363217088219384929328103085420037536 * μ ^ 8)
  b32 := (-1129696757538462557056885297140740865743209 / 6126281656262957563061352298250576435580000
    - 114087395077401272266586917473888347194963 / 98020506500207321008981636772009222969280 * μ +
    1380456707730453842413025349320752731099271 / 1568328104003317136143706188352147567508480 * μ ^
    2 + 56015815254691562002811478614515679964785237 / 38267205737680938121906430995792400647206912
    * μ ^ 3 + 4460548344670624319381045608989872072324045 /
    4783400717210117265238303874474050080900864 * μ ^ 4 - 133704845870114755661545702856577621578925
    / 6377867622946823020317738499298733441201152 * μ ^ 5 -
    5226801445957035905418147902965728985652125 / 6377867622946823020317738499298733441201152 * μ ^
    6 - 123143124968240781757199565530161781845625 / 311115493802284049771596999965791875180544 * μ
    ^ 7 - 22679323386261100122819547025094788546875 / 99654181608544109692464664051542710018768 * μ
    ^ 8)
  b23 := (-144119397291152210468508810262473116409373 / 2042093885420985854353784099416858811860000
    - 114699041016414275161182082698132259241783 / 163367510833678868348302727953348704948800 * μ +
    447940627560606026737748349445107081498931 / 522776034667772378714568729450715855836160 * μ ^ 2
    + 65728048314322796158838163377673050512886219 / 38267205737680938121906430995792400647206912 *
    μ ^ 3 + 257194734821232065154873007522706810020625 / 1594466905736705755079434624824683360300288
    * μ ^ 4 + 720298055410574327628454836345449952591425 /
    490605201765140232332133730715287187784704 * μ ^ 5 -
    10727243651039076730488852724920928747247875 / 6377867622946823020317738499298733441201152 * μ ^
    6 + 815510162982995849785755339913536314970625 / 12755735245893646040635476998597466882402304 *
    μ ^ 7 - 33331689882077153765340758388927120859375 / 99654181608544109692464664051542710018768 *
    μ ^ 8)
  b14 := (11586716473228923737130136265891295002107 / 4084187770841971708707568198833717623720000 -
    2566993732096550942955552949109899870199 / 11953720304903331830363614240488929630400 * μ +
    235622213971504277165011292690133658598567 / 627331241601326854457482475340859027003392 * μ ^ 2
    + 22298757609327175903810572673047557758874217 / 25511470491787292081270953997194933764804608 *
    μ ^ 3 + 1782359270712029182028295119477061061481045 /
    2391700358605058632619151937237025040450432 * μ ^ 4 -
    5248305414249470824950041231428225520033775 / 12755735245893646040635476998597466882402304 * μ ^
    5 - 11962657485310221259219091285330718217486125 / 12755735245893646040635476998597466882402304
    * μ ^ 6 - 1101129645972077122745737448365746456941875 /
    1962420807060560929328534922861148751138816 * μ ^ 7 - 74057685878335571752546535815652984890625
    / 199308363217088219384929328103085420037536 * μ ^ 8)
  b05 := (171679143252196382564670962681190269426611 / 61262816562629575630613522982505764355800000
    - 70798308600384578542903887409115006464447 / 4901025325010366050449081838600461148464000 * μ +
    841040111303184322195408323089233492946297 / 15683281040033171361437061883521475675084800 * μ ^
    2 + 94454465821854893480746114686636253864803433 / 382672057376809381219064309957924006472069120
    * μ ^ 3 + 434740645355838042769304967024252452666123 /
    2391700358605058632619151937237025040450432 * μ ^ 4 +
    1472236077917446386523281107780850262908335 / 12755735245893646040635476998597466882402304 * μ ^
    5 - 10281326762260279401236501478851906918560875 / 12755735245893646040635476998597466882402304
    * μ ^ 6 + 182731949743985468980834302025225166274375 /
    25511470491787292081270953997194933764804608 * μ ^ 7 - 88380102613671975647035677424002692378125
    / 199308363217088219384929328103085420037536 * μ ^ 8)

/-- The jet's first coordinate is `cF`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jetF_eq (μ a b : ℝ) :
    poly3 (jet μ).F a b 0 = poly3 (cF μ) a b 0 := by
  simp only [PlanarFocus.Jet5.F, PlanarFocus.Jet.F2, PlanarFocus.Jet.F3, PlanarFocus.Jet5.F4,
    PlanarFocus.Jet5.F5, jet, cF, cF2, cF3, cF4, cF5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]

/-- The jet's second coordinate is `cG`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jetG_eq (μ a b : ℝ) :
    poly3 (jet μ).G a b 0 = poly3 (cG μ) a b 0 := by
  simp only [PlanarFocus.Jet5.G, PlanarFocus.Jet.G2, PlanarFocus.Jet.G3, PlanarFocus.Jet5.G4,
    PlanarFocus.Jet5.G5, jet, cG, cG2, cG3, cG4, cG5, poly3_cons, poly3_nil, List.cons_append,
    List.nil_append]

/-- The Lyapunov chain of the jet: `c30` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c30 (μ : ℝ) : (jet μ).c30 1 = (262012 / 331635 + 61043 / 66327
    * μ + 27460 / 66327 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c30]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `c21` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c21 (μ : ℝ) : (jet μ).c21 1 = (74294 / 110545 - 961 / 22109 *
    μ + 3070 / 22109 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c21]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `c12` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c12 (μ : ℝ) : (jet μ).c12 1 = (448 / 22109 + 8147 / 22109 * μ
    + 11200 / 22109 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c12]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `c03` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c03 (μ : ℝ) : (jet μ).c03 1 = (99922 / 331635 - 53857 / 66327
    * μ - 13190 / 66327 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c03]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d40` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d40 (μ : ℝ) : (jet μ).d40 1 = (-35129594201449 /
    133762276635650 + 5592285141919 / 26752455327130 * μ - 3478938377933 / 21401964261704 * μ ^ 2 -
    188327402145 / 823152471604 * μ ^ 3 - 3187655745075 / 21401964261704 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d40]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d31` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d31 (μ : ℝ) : (jet μ).d31 1 = (50526344733689 /
    200643414953475 + 151144224468141 / 428039285234080 * μ - 22480100344381 / 42803928523408 * μ ^
    2 - 7081879495945 / 85607857046816 * μ ^ 3 - 94133850075 / 411576235802 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d31]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d22` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d22 (μ : ℝ) : (jet μ).d22 1 = (48227827985473 /
    200643414953475 - 66334320892649 / 214019642617040 * μ - 6841891675595 / 5350491065426 * μ ^ 2 -
    35588728549495 / 42803928523408 * μ ^ 3 - 7180992417275 / 21401964261704 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d22]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d13` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d13 (μ : ℝ) : (jet μ).d13 1 = (-6533458794751 /
    200643414953475 + 37238602866015 / 85607857046816 * μ - 358022509819 / 3292609886416 * μ ^ 2 -
    29325637738975 / 85607857046816 * μ ^ 3 - 4301997369625 / 10700982130852 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `l1` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l1 (μ : ℝ) : (jet μ).l1 1 = (405175969 / 6050127850 -
    9696786981 / 19360409120 * μ - 78177547 / 148926224 * μ ^ 2 - 783010455 / 3872081824 * μ ^ 3 -
    114029875 / 484010228 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.l1]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r50 (μ : ℝ) : (jet μ).r50 1 = (4805556650086653013046110607 /
    19400599690374338743417626750 - 12096368754701241771285322531 / 62081919009197883978936405600 *
    μ - 43008412478386505463858982519 / 49665535207358307183149124480 * μ ^ 2 -
    96656896476657288734772075 / 827758920122638453052485408 * μ ^ 3 - 62793174610976573738802585 /
    206939730030659613263121352 * μ ^ 4 - 122902194703513865024053625 / 827758920122638453052485408
    * μ ^ 5 + 26843334040443151051077125 / 3311035680490553812209941632 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r50]
  rw [jv_c30, jv_c21, jv_d40, jv_d31]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r41 (μ : ℝ) : (jet μ).r41 1 = (-77529060215994058850546467771
    / 77602398761497354973670507000 - 667790512848648401376546325787 /
    124163838018395767957872811200 * μ - 20793231188605787736701759941 /
    4966553520735830718314912448 * μ ^ 2 - 4815511735247951372283373629 /
    827758920122638453052485408 * μ ^ 3 - 5843716065918741017331364655 /
    1655517840245276906104970816 * μ ^ 4 - 2418312862158211833951801775 /
    1655517840245276906104970816 * μ ^ 5 - 5762853790410168167188875 / 20189241954210693976889888 *
    μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r41]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r32 (μ : ℝ) : (jet μ).r32 1 = (-53378739025330915483274307209
    / 38801199380748677486835253500 - 176238155143985313068627051 / 413879460061319226526242704 * μ
    - 9867867860309449954476119379 / 8277589201226384530524854080 * μ ^ 2 -
    2386108987788121286561095279 / 413879460061319226526242704 * μ ^ 3 -
    4393225744234580007624268415 / 827758920122638453052485408 * μ ^ 4 - 508896690608202927893048425
    / 206939730030659613263121352 * μ ^ 5 - 748938293967002322072044375 /
    1655517840245276906104970816 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r32]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r23 (μ : ℝ) : (jet μ).r23 1 = (-2963903756163903674371385197 /
    9700299845187169371708813375 - 21130614429117214933190205169 / 20693973003065961326312135200 * μ
    - 3499729230787464421269152753 / 4138794600613192265262427040 * μ ^ 2 -
    1449965193852021739607837799 / 413879460061319226526242704 * μ ^ 3 - 38894063868125647202168775
    / 31836881543178402040480208 * μ ^ 4 - 1896633888885650806110220925 /
    827758920122638453052485408 * μ ^ 5 - 430520276048694601706625625 / 827758920122638453052485408
    * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r23]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r14 (μ : ℝ) : (jet μ).r14 1 = (7443434868512875450179988769 /
    38801199380748677486835253500 - 69570626419509755654878525883 / 62081919009197883978936405600 *
    μ + 4967877233778544977194843585 / 9933107041471661436629824896 * μ ^ 2 +
    6012372940293444943416397 / 20189241954210693976889888 * μ ^ 3 + 273458512989122680911543285 /
    827758920122638453052485408 * μ ^ 4 + 14912941143347453530248825 / 20189241954210693976889888 *
    μ ^ 5 + 986544630191018498650986125 / 3311035680490553812209941632 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r14]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r05 (μ : ℝ) : (jet μ).r05 1 = (402396681892951581168668519 /
    15520479752299470994734101400 - 21352239649808502391392250027 / 124163838018395767957872811200 *
    μ - 1440815913555607799094053161 / 24832767603679153591574562240 * μ ^ 2 +
    338197846229914027458874671 / 827758920122638453052485408 * μ ^ 3 + 709680998468179435412301515
    / 1655517840245276906104970816 * μ ^ 4 + 558626427718240518571515125 /
    1655517840245276906104970816 * μ ^ 5 + 39421914197025021464931875 / 51734932507664903315780338 *
    μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r05]
  rw [jv_c12, jv_c03, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `e50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e50 (μ : ℝ) : (jet μ).e50 1 = (-52782754694177314418966965141
    / 232807196284492064921011521000 - 485551365778763960491811887921 /
    372491514055187303873618433600 * μ - 365421745906981251498508657439 /
    372491514055187303873618433600 * μ ^ 2 - 1169387547420841923707364981 /
    827758920122638453052485408 * μ ^ 3 - 3179736570459170975544246889 /
    4966553520735830718314912448 * μ ^ 4 - 2074492544054262915544833605 /
    4966553520735830718314912448 * μ ^ 5 + 695226689780272571906759425 /
    2483276760367915359157456224 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e50]
  rw [jv_r41, jv_r23, jv_r05]
  ring

/-- The Lyapunov chain of the jet: `e41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e41 (μ : ℝ) : (jet μ).e41 1 = (-4805556650086653013046110607 /
    19400599690374338743417626750 + 12096368754701241771285322531 / 62081919009197883978936405600 *
    μ + 43008412478386505463858982519 / 49665535207358307183149124480 * μ ^ 2 +
    96656896476657288734772075 / 827758920122638453052485408 * μ ^ 3 + 62793174610976573738802585 /
    206939730030659613263121352 * μ ^ 4 + 122902194703513865024053625 / 827758920122638453052485408
    * μ ^ 5 - 26843334040443151051077125 / 3311035680490553812209941632 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e41]
  rw [jv_r50]
  ring

/-- The Lyapunov chain of the jet: `e32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e32 (μ : ℝ) : (jet μ).e32 1 = (-3915824102863049442899427799 /
    58201799071123016230252880250 - 106096322586968649582355115561 / 186245757027593651936809216800
    * μ - 13380819519473608861995564581 / 37249151405518730387361843360 * μ ^ 2 -
    257856500464064561563362819 / 413879460061319226526242704 * μ ^ 3 + 12753635511409126361506715 /
    77602398761497354973670507 * μ ^ 4 - 779381033449169768967190675 / 2483276760367915359157456224
    * μ ^ 5 + 2092482232560906772049014375 / 2483276760367915359157456224 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e32]
  rw [jv_r23, jv_r05]
  ring

/-- The Lyapunov chain of the jet: `e23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e23 (μ : ℝ) : (jet μ).e23 1 = (14934285824637691378905422353 /
    116403598142246032460505760500 + 37410599145201382022717673887 / 93122878513796825968404608400 *
    μ + 1778775823656944012171481895 / 1146127735554422473457287488 * μ ^ 2 +
    2579422780741435864030639429 / 1241638380183957679578728112 * μ ^ 3 +
    5397916538010205187445109775 / 2483276760367915359157456224 * μ ^ 4 + 8099985709124574268167975
    / 7959220385794600510120052 * μ ^ 5 + 695251625886116019969890125 / 4966553520735830718314912448
    * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e23]
  rw [jv_r50, jv_r32]
  ring

/-- The Lyapunov chain of the jet: `e14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e14 (μ : ℝ) : (jet μ).e14 1 = (402396681892951581168668519 /
    15520479752299470994734101400 - 21352239649808502391392250027 / 124163838018395767957872811200 *
    μ - 1440815913555607799094053161 / 24832767603679153591574562240 * μ ^ 2 +
    338197846229914027458874671 / 827758920122638453052485408 * μ ^ 3 + 709680998468179435412301515
    / 1655517840245276906104970816 * μ ^ 4 + 558626427718240518571515125 /
    1655517840245276906104970816 * μ ^ 5 + 39421914197025021464931875 / 51734932507664903315780338 *
    μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e14]
  rw [jv_r05]
  ring

/-- The Lyapunov chain of the jet: `e05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e05 (μ : ℝ) : (jet μ).e05 1 = (7538267043736756407270878399 /
    582017990711230162302528802500 + 358354275839334795055506273197 / 931228785137968259684046084000
    * μ + 15518542225765090740266505557 / 29799321124414984309889474688 * μ ^ 2 +
    1915633850261929945616468177 / 2483276760367915359157456224 * μ ^ 3 +
    1995091507410608466431117939 / 2483276760367915359157456224 * μ ^ 4 +
    214673288124133170607747395 / 827758920122638453052485408 * μ ^ 5 - 35725477405718283214679575 /
    9933107041471661436629824896 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e05]
  rw [jv_r50, jv_r32, jv_r14]
  ring

/-- The Lyapunov chain of the jet: `r60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r60 (μ : ℝ) : (jet μ).r60 1 =
    (-1741105837907893688180567631088120114487129 / 91894224843944363445920284473758646533700000 +
    10862080086391145898901644908459959220402533 / 4901025325010366050449081838600461148464000 * μ +
    34021852337247362693494254838373034022921157 / 11762460780024878521077796412641106756313600 * μ
    ^ 2 + 2121751769377887145781045248505539493944209709 /
    574008086065214071828596464936886009708103680 * μ ^ 3 +
    18965745222379734354788205250686758845999181 / 7175101075815175897857455811711075121351296 * μ ^
    4 + 2449399058493499817549535977155999219085915 / 1471815605295420696996401192145861563354112 *
    μ ^ 5 + 130344748109770162348743742478937077960025 / 1594466905736705755079434624824683360300288
    * μ ^ 6 + 9946613756940261699732374622484931408042875 /
    38267205737680938121906430995792400647206912 * μ ^ 7 -
    571922789119485264818108737367220408940625 / 9566801434420234530476607748948100161801728 * μ ^
    8) := by
  simp only [PlanarFocus.Jet5.r60]
  rw [jv_c30, jv_c21, jv_d40, jv_d31, jv_e50, jv_e41]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r51 (μ : ℝ) : (jet μ).r51 1 =
    (-7914903943205455742676118472742868056570283 / 22973556210986090861480071118439661633425000 -
    27808587732137631616045617966241602020116963 / 7351537987515549075673622757900691722696000 * μ -
    211308976913409005241044342454605058834683 / 47814881219613327321454456961955718521600 * μ ^ 2 -
    29348122927106881251727404145352095663581361 / 28700404303260703591429823246844300485405184 * μ
    ^ 3 + 5938495445577920547826055366018057256171485 / 28700404303260703591429823246844300485405184
    * μ ^ 4 - 2907629823837191313356568129247889198432825 /
    4783400717210117265238303874474050080900864 * μ ^ 5 +
    1212278878661606746614836181921213359255975 / 597925089651264658154787984309256260112608 * μ ^ 6
    + 14838903920569952815815503159742422049624625 / 9566801434420234530476607748948100161801728 * μ
    ^ 7 + 1327155019212618161988823133128818061271875 / 9566801434420234530476607748948100161801728
    * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r51]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22, jv_e50, jv_e41, jv_e32]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r42 (μ : ℝ) : (jet μ).r42 1 =
    (-7213380707291560542961724552342543224486757 / 18378844968788872689184056894751729306740000 -
    39281705291343931419241138580228895542457253 / 14703075975031098151347245515801383445392000 * μ
    + 761458321691668466186272461157212819396329 / 95629762439226654642908913923911437043200 * μ ^ 2
    + 9421323559992903869413668781439005680363706421 / 574008086065214071828596464936886009708103680
    * μ ^ 3 + 391978839816017356107164272450950453450521197 /
    28700404303260703591429823246844300485405184 * μ ^ 4 +
    245681168058904983061202721257260393363772135 / 19133602868840469060953215497896200323603456 * μ
    ^ 5 + 22926654109349547328096508156065242005485925 / 4783400717210117265238303874474050080900864
    * μ ^ 6 + 141176200670756907820728960226668238245813875 /
    38267205737680938121906430995792400647206912 * μ ^ 7 +
    5056491015066125061226808041423803853410625 / 4783400717210117265238303874474050080900864 * μ ^
    8) := by
  simp only [PlanarFocus.Jet5.r42]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e50, jv_e41, jv_e32,
    jv_e23]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r33 (μ : ℝ) : (jet μ).r33 1 =
    (-412357222045059534848347437547963655632043 / 765785207032869695382669037281322054447500 -
    804519670292922429376267403449222998667089 / 204209388542098585435378409941685881186000 * μ +
    9702425272650692373338939634176001778251833 / 1960410130004146420179632735440184459385600 * μ ^
    2 + 70211418503723793496322138676357879885474619 / 4783400717210117265238303874474050080900864 *
    μ ^ 3 + 82579034675403606752189629168645979914038319 /
    4783400717210117265238303874474050080900864 * μ ^ 4 +
    32203610851863277061805563431812702355418435 / 2391700358605058632619151937237025040450432 * μ ^
    5 + 58064595450970989584087196477703778070854375 / 4783400717210117265238303874474050080900864 *
    μ ^ 6 + 7759274606489219074142383932858034381848625 /
    1594466905736705755079434624824683360300288 * μ ^ 7 +
    5568280081769133087783548873980263186873125 / 4783400717210117265238303874474050080900864 * μ ^
    8) := by
  simp only [PlanarFocus.Jet5.r33]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e41, jv_e32, jv_e23,
    jv_e14]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r24 (μ : ℝ) : (jet μ).r24 1 =
    (-12180518309745200696385981413608132288063 / 56550292211658069812874021214620705559200 +
    13514665457476478146643857120514330013299569 / 14703075975031098151347245515801383445392000 * μ
    + 25696150236259988607859959135143085704156171 / 3920820260008292840359265470880368918771200 * μ
    ^ 2 + 7333208363795115756111446468846778151788498499 /
    574008086065214071828596464936886009708103680 * μ ^ 3 +
    264291462662326612786338031576202483980108615 / 14350202151630351795714911623422150242702592 * μ
    ^ 4 + 91707140726068812160633027725705331401548475 / 6377867622946823020317738499298733441201152
    * μ ^ 5 + 2833319487063754341017876995402821667432925 /
    597925089651264658154787984309256260112608 * μ ^ 6 +
    219558503972044424250923117826631479510023125 / 38267205737680938121906430995792400647206912 * μ
    ^ 7 + 13690444561330954511125969428391815075006875 / 9566801434420234530476607748948100161801728
    * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r24]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13, jv_e32, jv_e23, jv_e14, jv_e05]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r15 (μ : ℝ) : (jet μ).r15 1 =
    (1007253291260018043103435835506948188150469 / 22973556210986090861480071118439661633425000 -
    582472099584161486217525122797261243331393 / 7351537987515549075673622757900691722696000 * μ +
    128850987783659145320855879143846637842809 / 40841877708419717087075681988337176237200 * μ ^ 2 +
    1024867587637799007117370845160821961636323779 / 143502021516303517957149116234221502427025920 *
    μ ^ 3 + 262342899366843516856176746232647998262823445 /
    28700404303260703591429823246844300485405184 * μ ^ 4 +
    9321360198546124667894750729294492833494185 / 1594466905736705755079434624824683360300288 * μ ^
    5 + 10587756401163533963001083666997485544413075 / 4783400717210117265238303874474050080900864 *
    μ ^ 6 - 322954610362279024602161126693013946472875 / 735907802647710348498200596072930781677056
    * μ ^ 7 + 3520930087656173273278867387860123101119375 /
    9566801434420234530476607748948100161801728 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r15]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13, jv_e23, jv_e14, jv_e05]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r06` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r06 (μ : ℝ) : (jet μ).r06 1 =
    (1176389231216393846257174992697078436246873 / 91894224843944363445920284473758646533700000 -
    39076672514173476791479015895751780658309 / 980205065002073210089816367720092229692800 * μ +
    1207922731831552299823432820540762210362487 / 2352492156004975704215559282528221351262720 * μ ^
    2 + 919222210127373668861345905929238360312339547 /
    574008086065214071828596464936886009708103680 * μ ^ 3 +
    69673890706365475085721444461878466304934093 / 28700404303260703591429823246844300485405184 * μ
    ^ 4 + 6186942737015224130437502570675915406237315 / 6377867622946823020317738499298733441201152
    * μ ^ 5 - 458020457656972225108532613126620288433325 /
    2391700358605058632619151937237025040450432 * μ ^ 6 -
    14056107743524295786396515060531841248103875 / 38267205737680938121906430995792400647206912 * μ
    ^ 7 - 704419452677119523068171571302279085890625 / 597925089651264658154787984309256260112608 *
    μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r06]
  rw [jv_c12, jv_c03, jv_d13, jv_e14, jv_e05]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `f60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f60 (μ : ℝ) : (jet μ).f60 1 =
    (-4364336327540443574099298066818458234300153 / 45947112421972181722960142236879323266850000 -
    7145402316165732805172659391854146206575993 / 7351537987515549075673622757900691722696000 * μ +
    527198221442492432708385327856407131857499 / 2613880173338861893572843647253579279180800 * μ ^ 2
    + 643766083519373834434521968193143227200178753 / 287004043032607035914298232468443004854051840
    * μ ^ 3 + 172006166279544085886857229701534665087036629 /
    57400808606521407182859646493688600970810368 * μ ^ 4 +
    19086687207888153250711082496816097219156055 / 9566801434420234530476607748948100161801728 * μ ^
    5 + 98636570311883765455926742722438162907776125 / 57400808606521407182859646493688600970810368
    * μ ^ 6 + 3768701978369775857601617812367482654558125 /
    6377867622946823020317738499298733441201152 * μ ^ 7 +
    10416365188637924523051239394969204349264375 / 57400808606521407182859646493688600970810368 * μ
    ^ 8) := by
  simp only [PlanarFocus.Jet5.f60]
  rw [jv_r51, jv_r33, jv_r15]
  ring

/-- The Lyapunov chain of the jet: `f51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f51 (μ : ℝ) : (jet μ).f51 1 =
    (-1926633463545309627822732728335701103121461 / 91894224843944363445920284473758646533700000 -
    8065550690069547472827343533980720903162801 / 4901025325010366050449081838600461148464000 * μ -
    43323620784269248742089898145204471273713393 / 47049843120099514084311185650564427025254400 * μ
    ^ 2 - 124289155545741914609978309601809924979525259 /
    574008086065214071828596464936886009708103680 * μ ^ 3 +
    6788100451371713210902601982539536932991327 / 7175101075815175897857455811711075121351296 * μ ^
    4 + 16458916620485581724380043641325451895793215 / 19133602868840469060953215497896200323603456
    * μ ^ 5 + 18355814370833722223822827243108344443967625 /
    38267205737680938121906430995792400647206912 * μ ^ 6 +
    11315088412427310902663336368956641626677875 / 38267205737680938121906430995792400647206912 * μ
    ^ 7 - 252490182138384800950720616172148842221875 / 1471815605295420696996401192145861563354112 *
    μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f51]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `f42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f42 (μ : ℝ) : (jet μ).f42 1 =
    (-323631564963492186226360982982031665395636 / 2871694526373261357685008889804957704178125 -
    3012765232971353042998067676976655043867799 / 2940615195006219630269449103160276689078400 * μ +
    22072120099881970324141104031985279011161497 / 7841640520016585680718530941760737837542400 * μ ^
    2 + 259754858149206988695275365663273769989805383 / 35875505379075879489287279058555375606756480
    * μ ^ 3 + 255040001696527168556372816869292969002469201 /
    28700404303260703591429823246844300485405184 * μ ^ 4 +
    30083845723750825532744907809848090427950495 / 4783400717210117265238303874474050080900864 * μ ^
    5 + 26413369417766019170029787937232916386560175 / 6377867622946823020317738499298733441201152 *
    μ ^ 6 + 4769853471189507475649764287891230460349625 /
    4783400717210117265238303874474050080900864 * μ ^ 7 + 757434180785442196755201355153365523999375
    / 1594466905736705755079434624824683360300288 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f42]
  rw [jv_r33, jv_r15]
  ring

/-- The Lyapunov chain of the jet: `f33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f33 (μ : ℝ) : (jet μ).f33 1 =
    (1543051831437164462768505804176274695400071 / 27568267453183309033776085342127593960110000 -
    28266395246402447419250151029584386574913587 / 22054613962546647227020868273702075168088000 * μ
    - 39120529062435815372304272248813508632205891 / 17643691170037317781616694618961660134470400 *
    μ ^ 2 - 2025190748112588874475179756368433299183639683 /
    861012129097821107742894697405329014562155520 * μ ^ 3 +
    52829317296434278899177453998555834557191439 / 86101212909782110774289469740532901456215552 * μ
    ^ 4 - 3080545302295639396955078169595468108845955 / 9566801434420234530476607748948100161801728
    * μ ^ 5 - 3397737005527893643134987230646463859878075 /
    14350202151630351795714911623422150242702592 * μ ^ 6 -
    10407826050258817750112572703780155504131125 / 57400808606521407182859646493688600970810368 * μ
    ^ 7 - 8319413289562238522115138111967002909726875 / 9566801434420234530476607748948100161801728
    * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f33]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `f24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f24 (μ : ℝ) : (jet μ).f24 1 =
    (1007253291260018043103435835506948188150469 / 45947112421972181722960142236879323266850000 -
    582472099584161486217525122797261243331393 / 14703075975031098151347245515801383445392000 * μ +
    128850987783659145320855879143846637842809 / 81683755416839434174151363976674352474400 * μ ^ 2 +
    1024867587637799007117370845160821961636323779 / 287004043032607035914298232468443004854051840 *
    μ ^ 3 + 262342899366843516856176746232647998262823445 /
    57400808606521407182859646493688600970810368 * μ ^ 4 +
    9321360198546124667894750729294492833494185 / 3188933811473411510158869249649366720600576 * μ ^
    5 + 10587756401163533963001083666997485544413075 / 9566801434420234530476607748948100161801728 *
    μ ^ 6 - 322954610362279024602161126693013946472875 / 1471815605295420696996401192145861563354112
    * μ ^ 7 + 3520930087656173273278867387860123101119375 /
    19133602868840469060953215497896200323603456 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f24]
  rw [jv_r15]
  ring

/-- The Lyapunov chain of the jet: `f15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f15 (μ : ℝ) : (jet μ).f15 1 =
    (4844128532669597162260475352120899653855463 / 91894224843944363445920284473758646533700000 -
    2991912758892465810031696453957997220531277 / 4901025325010366050449081838600461148464000 * μ -
    13721066785617831207083692959494484122144299 / 9409968624019902816862237130112885405050880 * μ ^
    2 - 1078240403704771562309721032974491208652344903 /
    574008086065214071828596464936886009708103680 * μ ^ 3 -
    33341491988640315177041784471026716811027939 / 28700404303260703591429823246844300485405184 * μ
    ^ 4 - 9913425389951802320403834544108565175066055 / 6377867622946823020317738499298733441201152
    * μ ^ 5 - 28812415647979761721929198872628758929941425 /
    38267205737680938121906430995792400647206912 * μ ^ 6 -
    35317809912891868388792226051973414282824625 / 38267205737680938121906430995792400647206912 * μ
    ^ 7 - 18115204539629851796185904796700554981734375 /
    19133602868840469060953215497896200323603456 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f15]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `k6` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_k6 (μ : ℝ) : (jet μ).k6 1 = (-56505351333715821271317529568059
    / 1415726428072250079236328949370000 + 969377706264771892635283580266997 /
    1698871713686700095083594739244000 * μ + 8574737787638132655570249165855541 /
    4349111587037952243414002532464640 * μ ^ 2 + 1513426031685820318898284677319235 /
    434911158703795224341400253246464 * μ ^ 3 + 991912168766358864596829224209227 /
    276349798759703215466931410917024 * μ ^ 4 + 11161933749358597921772088645197165 /
    4421596780155251447470902574672384 * μ ^ 5 + 29788631994393867563878729356294025 /
    53059161361863017369650830896068608 * μ ^ 6 + 4913380637046367240537762006981125 /
    8843193560310502894941805149344768 * μ ^ 7 - 6137145571367111798606461363390625 /
    26529580680931508684825415448034304 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.k6]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `l2` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l2 (μ : ℝ) : (jet μ).l2 1 = (-56505351333715821271317529568059
    / 707863214036125039618164474685000 + 969377706264771892635283580266997 /
    849435856843350047541797369622000 * μ + 8574737787638132655570249165855541 /
    2174555793518976121707001266232320 * μ ^ 2 + 1513426031685820318898284677319235 /
    217455579351897612170700126623232 * μ ^ 3 + 991912168766358864596829224209227 /
    138174899379851607733465705458512 * μ ^ 4 + 11161933749358597921772088645197165 /
    2210798390077625723735451287336192 * μ ^ 5 + 29788631994393867563878729356294025 /
    26529580680931508684825415448034304 * μ ^ 6 + 4913380637046367240537762006981125 /
    4421596780155251447470902574672384 * μ ^ 7 - 6137145571367111798606461363390625 /
    13264790340465754342412707724017152 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.l2]
  rw [jv_k6]
  ring

/-! ## The Bautin point of the path -/

/-- **The Bautin quartic** of the path: `l₁(J) = −𝔔(μ)/96802045600`,
`hopfNum = −𝔔(μ)/5538336400`. -/
def bautinQuartic (μ : ℝ) : ℝ :=
  22805975000 * μ ^ 4 + 19575261375 * μ ^ 3 + 50815405550 * μ ^ 2 + 48483934905 * μ -
    6482815504

/-- `l₁(J) = −𝔔(μ)/96802045600` along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1 (μ : ℝ) :
    (jet μ).l1 1 = -bautinQuartic μ / 96802045600 := by
  rw [jv_l1, bautinQuartic]; ring

/-- The integer numerator of `l₂(J)` (coefficients from the constant term up). -/
def l2Num : List ℤ := [-1323581349640959397459341812602214016,
    18922252826288347344240735486811781440, 65382375630740761498723149889648500125,
    115398734916043799315994206645591668750, 119029460251963063751619506905107240000,
    83714503120189484413290664838978737500, 18617894996496167227424205847683765625,
    18425177388923877152016607526179218750, -7671431964208889748258076704238281250]

/-- `l₂(J) = l2Num(μ)/l2Den` along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l2 (μ : ℝ) :
    (jet μ).l2 1 = zeval l2Num μ / 16580987925582192928015884655021440000 := by
  rw [jv_l2]
  simp only [l2Num, zeval]
  push_cast
  ring

/-- **`l₂ > 0` on `[11/100, 12/100)`** (a Möbius sign certificate, `decide +kernel`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem l2Num_pos {μ : ℝ} (h1 : 11 / 100 ≤ μ) (h2 : μ < 12 / 100) :
    0 < zeval l2Num μ :=
  zeval_pos_of_zmob_Ico (A := 11) (B := 12) (C := 100) (by norm_num) (by decide +kernel)
    (by push_cast; linarith) (by push_cast; linarith)

/-- **The positive roots of the Bautin quartic lie in `(11/100, 12/100)`** (`𝔔` increases on
`μ ≥ 0`, `𝔔(11/100) < 0 < 𝔔(12/100)`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinQuartic_root_mem {μ : ℝ} (hμ : 0 < μ)
    (hq : bautinQuartic μ = 0) : 11 / 100 < μ ∧ μ < 12 / 100 := by
  unfold bautinQuartic at hq
  constructor
  · by_contra h
    push Not at h
    have e2 : μ ^ 2 ≤ (11 / 100) ^ 2 := pow_le_pow_left₀ hμ.le h 2
    have e3 : μ ^ 3 ≤ (11 / 100) ^ 3 := pow_le_pow_left₀ hμ.le h 3
    have e4 : μ ^ 4 ≤ (11 / 100) ^ 4 := pow_le_pow_left₀ hμ.le h 4
    nlinarith
  · by_contra h
    push Not at h
    have e2 : (12 / 100) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
    have e3 : (12 / 100) ^ 3 ≤ μ ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    have e4 : (12 / 100) ^ 4 ≤ μ ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    nlinarith

/-- **The path has a Bautin point**: the quartic has a root in `(11/100, 12/100)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_bautinQuartic_root :
    ∃ μ : ℝ, 11 / 100 < μ ∧ μ < 12 / 100 ∧ bautinQuartic μ = 0 := by
  have hc : ContinuousOn bautinQuartic (Set.Icc (11 / 100) (12 / 100)) := by
    unfold bautinQuartic; fun_prop
  have h := intermediate_value_Ioo (by norm_num : (11 / 100 : ℝ) ≤ 12 / 100) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo (bautinQuartic (11 / 100)) (bautinQuartic (12 / 100)) := by
    constructor <;> norm_num [bautinQuartic]
  obtain ⟨μ, ⟨h1, h2⟩, hμ⟩ := h h0
  exact ⟨μ, h1, h2, hμ⟩

/-- `l₁(J) = 0` at a Bautin point of the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1_eq_zero {μ : ℝ} (hq : bautinQuartic μ = 0) :
    (jet μ).l1 1 = 0 := by
  rw [jet_l1, hq]; simp

/-- **`l₂(J) > 0` at a Bautin point of the path.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l2_pos {μ : ℝ} (hμ : 0 < μ) (hq : bautinQuartic μ = 0) :
    0 < (jet μ).l2 1 := by
  obtain ⟨h1, h2⟩ := bautinQuartic_root_mem hμ hq
  rw [jet_l2]
  exact div_pos (l2Num_pos h1.le h2) (by norm_num)

/-- **The first Lyapunov numerator of the path**: `hopfNum = −𝔔(μ)/5538336400` (the data
`M = 85/122`, `D = 10/61`, `ω_q = 1`, `ω = 1`, `K = 6/5`, `Q_δ = −1`, `n_q/E* = μ`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem bpath_hopfNumAt (hμ : 0 < μ) :
    (bpath μ).hopfNumAt = -bautinQuartic μ / 5538336400 := by
  obtain ⟨-, -, h3, h4⟩ := bpath_data hμ
  rw [Model.hopfNumAt, bpath_hopfFreq hμ, bpath_emf, show (bpath μ).δ = 0 from rfl, h3, h4,
    show (bpath μ).q.ωq = 1 from rfl, show (bpath μ).q.M = 85 / 122 from rfl,
    show (bpath μ).q.D = 10 / 61 from rfl, show (bpath μ).q.nq = μ from rfl, div_one]
  simp only [hopfNum, hopfNum1, hopfNum2, hopfNum3, bautinQuartic]
  ring

end Bautin

open Bautin

/-- **The Bautin point of the path is unstable**: at a positive root of the Bautin quartic
(`ℓ₁ = 0`; the root lies in `(11/100, 12/100)` and exists, `Bautin.exists_bautinQuartic_root`),
the model `Bautin.bpath μ` is a weak focus of the second order with `l₂ > 0` in the critical chart
(the approximate centre manifold `Bautin.manifold μ`, invariance defect `O(‖u‖⁵)`, the quintic jet
`Bautin.jet μ`; `mem_den_unstable_of_secondLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem bautinPath_mem_den_unstable_of_bautinQuartic_eq_zero {μ : ℝ}
    (hμ : 0 < μ) (hq : bautinQuartic μ = 0) :
    connection% (bpath μ ∈ family.den (.flow .unstable)) := by
  have hM : 0 < (bpath μ).q.M := by norm_num [bpath]
  have hD : 0 < (bpath μ).q.D := by norm_num [bpath]
  have hω : 0 < (bpath μ).q.ωq := by norm_num [bpath]
  have hE : (bpath μ).q.emf (bpath μ).Qf ≠ 0 := by rw [bpath_emf]; norm_num
  refine mem_den_unstable_of_secondLyapunov_pos (bpath μ) ⟨hM, hD, hω, hE⟩ (bpath_isHopf hμ)
    (bpath_hopfFreq hμ) (isCriticalPair_C hμ) (isCritical_C hμ).isChart (rotL_rotL 1)
    ⟨contDiffAt_manifold μ, manifold_zero μ, fderiv_manifold_zero μ, critP_manifold μ⟩
    (isOrder_defect hμ) (J := jet μ) ⟨?_, ?_⟩ ⟨jet_l1_eq_zero hq, jet_l2_pos hμ hq⟩
  · refine ((G0_sub_jet hμ).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => (bpath μ).field x - fderiv ℝ (bpath μ).field 0 x) = fnl μ from rfl,
      chartField_eq hμ, jetF_eq]
    simp only [PlanarFocus.frameX_apply, PlanarFocus.frameY_apply, PiLp.add_apply, rotL_apply0,
      G0, pv]
    ring_nf
  · refine ((G1_sub_jet hμ).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => (bpath μ).field x - fderiv ℝ (bpath μ).field 0 x) = fnl μ from rfl,
      chartField_eq hμ, jetG_eq]
    simp only [PlanarFocus.frameX_apply, PlanarFocus.frameY_apply, PiLp.add_apply, rotL_apply0,
      rotL_apply1, G1, pv]
    ring_nf

/-- **Below the Bautin point the path is subcritical**: `𝔔(μ) < 0` (`0 < μ < μ*`) gives
`hopfNum > 0`, an unstable Hopf point (`mem_den_unstable_of_hopfNum_pos`). -/
@[tmio TM, powerlib_domain] theorem bautinPath_mem_den_unstable_of_bautinQuartic_neg {μ : ℝ}
    (hμ : 0 < μ) (hq : bautinQuartic μ < 0) :
    connection% (bpath μ ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_hopfNum_pos (bpath μ) (by norm_num [bpath]) (by norm_num [bpath])
    (by norm_num [bpath]) (by rw [bpath_emf]; norm_num) (bpath_isHopf hμ)
    (by rw [bpath_hopfNumAt hμ]; linarith)

/-- **Above the Bautin point the path is supercritical**: `𝔔(μ) > 0` (`μ > μ*`) gives
`hopfNum < 0`, a locally asymptotically stable Hopf point
(`mem_den_locallyAsymptoticallyStable_of_hopfNum_neg`). -/
@[tmio TM, powerlib_domain] theorem
    bautinPath_mem_den_locallyAsymptoticallyStable_of_bautinQuartic_pos {μ : ℝ} (hμ : 0 < μ)
    (hq : 0 < bautinQuartic μ) :
    connection% (bpath μ ∈ family.den (.flow .locallyAsymptoticallyStable)) :=
  mem_den_locallyAsymptoticallyStable_of_hopfNum_neg (bpath μ) (by norm_num [bpath])
    (by norm_num [bpath]) (by norm_num [bpath]) (by rw [bpath_emf]; norm_num) (bpath_isHopf hμ)
    (by rw [bpath_hopfNumAt hμ]; linarith)

end QVDroop
end powerlib.GFM
