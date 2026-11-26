import theorem.GridTiedConverter.GFM.QVDroopBautin
import theorem.GridTiedConverter.GFM.QVDroopVirtualHopf

/-! # Grid-forming converter with Q–V droop and a virtual impedance: a path of Hopf points and its
Bautin point

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`, unchanged (state
  `(δ, Δω, Q_f)`, quasi-static line behind the virtual impedance `Z_v`, terminal-measured
  export-positive powers `P_t`, `Q_t`, `E = E₀ − n_q (Q_f − Q_ref)`), read about a selected point
  on `QVDroopVirtual.family`. Excluded as there.
* The family laws: a Hopf point of `theorem/GridTiedConverter/GFM/QVDroopVirtualHopf.lean`
  (`Model.IsHopf`; `M, D, ω_q > 0`, `E* ≠ 0`) with a critical pair at its frequency, read in any
  chart of the critical plane with a linear part `L₂`, `L₂² = −ω²`.
* The path `QVDroopVirtual.Bautin.bpath μ`, `μ > 0`: `M = 85/122`, `D = 10/61`, `ω_q = 1`,
  `n_q = μ`, `E₀ = 1`, `V = 75μ/u`, `R_g = 225μ/(4u)`, `X_g = 225μ/(8u)`, `R_v = 15μ/(4u)`,
  `X_v = 15μ/(8u)` (`u = 16 + 35μ`; `X_v > 0`, a genuinely inductive virtual impedance,
  `|Z_v| ≠ |Z_g|`), `P_ref = 4(4 − 25μ²)/(5μu)`, `Q_ref = Q_f* = 2(4 − 25μ²)/(5μu)`, at `δ* = 0`
  (EMF `E* = 1`). Along the path the linear data are those of `theorem/GridTiedConverter/GFM/
  QVDroopBautin.lean` (`P_tδ = 1/2`, `n_q P_tE = 2/5`, `Q_tδ = −1`, `K_t = 6/5`; `A = C = 1`,
  `G = 0`, `ω = 1`) and the curvatures are fixed, `ρ = P_tδδ = 7/8`, `τ = Q_tδδ = 7/16`; only
  `μ = n_q/E*` changes the nonlinear terms, so every point of the path is a Hopf point
  (`Bautin.bpath_isHopf`) and the critical chart, `qC`, `pC` and the stable eigenvector are those
  of `QVDroopBautin` (`QVDroop.Bautin.critι_C`, `QVDroop.Bautin.critπ_C`, `QVDroop.Bautin.wsv`).
* The approximate centre manifold is `Bautin.manifold μ = H ∘ π`, `H(y) = h(y) w`, `h` a
  polynomial in `y` of degrees two to four with coefficients polynomial in `μ`.
* Level: exact for every `μ > 0`, as in `QVDroopBautin`: Taylor remainders of `cos`, `sin`;
  polynomial identities in `μ` (`ring`); the Bautin point is the positive root of a quartic
  `𝔔_v(μ)`, located in `(6/100, 7/100)`, and the sign of `l₂` there is a kernel-checked Möbius
  certificate. No floating point, sampling or search.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3; Carr, *Applications
of Centre Manifold Theory* (1981), §2.4–2.5. The generic laws are
`theorem/Dynamics/CenterReductionBautin.lean`, `theorem/Dynamics/HopfDichotomy.lean`,
`theorem/Dynamics/CenterManifoldChart.lean` and `theorem/Dynamics/PolySign.lean`; the Hopf data
and the first-coefficient laws are those of `QVDroopVirtualHopf` (`Model.hopf_data`,
`mem_den_unstable_of_hopfNum_pos`, `mem_den_locallyAsymptoticallyStable_of_hopfNum_neg`); the
chart and the truncation polynomials are read from `QVDroopBautin`. The path (the linear data and
the curvatures fixed, the line and the virtual impedance rational in `μ`), the centre manifold,
the jet and the Lyapunov chain were derived with SymPy over `ℚ(μ)` (untrusted, discovery
evidence only); every identity is checked here.

Results.
* The path: `QVDroopVirtual.Bautin.bpath`, `Bautin.bpath_emf`, `Bautin.bpath_zsq`,
  `Bautin.bpath_data` (with the curvatures), `Bautin.bpath_balance`, `Bautin.bpath_jacobian`,
  **`Bautin.bpath_isHopf`**, `Bautin.bpath_hopfFreq`, `Bautin.fderiv_field_zero`,
  `Bautin.A_apply`, `Bautin.fnl`, `Bautin.fnl_apply`, `Bautin.isCriticalPair_C`,
  `Bautin.isCritical_C`, `Bautin.A_wsv`.
* The manifold, the chart field, the truncations, the splits and the defect, as in
  `QVDroopBautin`: `Bautin.hL2` … `Bautin.hL4`, `Bautin.manifold`, `Bautin.chartField_eq`,
  `Bautin.G_eq`, `Bautin.F1v`, `Bautin.F2v`, `Bautin.low2_eq` … `Bautin.lowQ_eq`,
  `Bautin.split2_isBigO` … `Bautin.splitQ_isBigO`, `Bautin.F1_sub_low`, `Bautin.F2_sub_low`,
  `Bautin.G0_sub_jet`, `Bautin.G1_sub_jet`, `Bautin.main_eq_high`, `Bautin.defect_eq`,
  **`Bautin.isOrder_defect`**.
* The jet `Bautin.jet`, the chain `Bautin.jv_c30` … `Bautin.jv_l2`, **`Bautin.jet_l1`**
  (`l₁(J) = −𝔔_v(μ)/774416364800`, `Bautin.bautinQuartic`), `Bautin.jet_l2`, `Bautin.l2Num`,
  **`Bautin.l2Num_pos`** (`l₂ > 0` on `[6/100, 7/100)`), `Bautin.bautinQuartic_root_mem`,
  `Bautin.exists_bautinQuartic_root`, `Bautin.jet_l1_eq_zero`, `Bautin.jet_l2_pos`,
  `Bautin.bpath_hopfNumAt` (`hopfNum = −𝔔_v(μ)/44306691200`).

Family and connection conclusions.
No new family: connection conclusions on `QVDroopVirtual.family`.
* `QVDroopVirtual.mem_den_unstable_of_secondLyapunov_pos`,
  `QVDroopVirtual.mem_den_locallyAsymptoticallyStable_of_secondLyapunov_neg`: the second-coefficient
  laws at a Hopf point, in any chart of the critical plane.
* **`QVDroopVirtual.bautinPath_mem_den_unstable_of_bautinQuartic_eq_zero`**: the Bautin point of
  the path (the unique positive root `μ* ∈ (6/100, 7/100)` of `𝔔_v`) is unstable, `l₂ > 0`.
* `QVDroopVirtual.bautinPath_mem_den_unstable_of_bautinQuartic_neg`,
  `QVDroopVirtual.bautinPath_mem_den_locallyAsymptoticallyStable_of_bautinQuartic_pos`: every
  point of the path is decided; it is unstable iff `𝔔_v(μ) ≤ 0`.
* Not decided here: the Bautin set of the virtual-impedance Hopf surface off this path.
-/

noncomputable section
namespace powerlib.GFM.QVDroopVirtual

open Complex Matrix Polynomial Filter Topology Asymptotics
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)
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

open QVDroop.Bautin (qC pC critι_C pC_apply critπ_C wsv critπ_wsv sub_critP lin0 lin2 pv lowF2 lowF3
  lowFC lowFS lowFQ)

/-- **The path of Hopf points with a virtual impedance**, parametrised by `μ = n_q/E*` (`δ* = 0`,
`E* = 1`). -/
def bpath (μ : ℝ) : Model :=
  ⟨⟨85 / 122, 10 / 61, 1, μ, 1, 2 * (4 - 25 * μ ^ 2) / (5 * μ * (16 + 35 * μ)),
    4 * (4 - 25 * μ ^ 2) / (5 * μ * (16 + 35 * μ)), 75 * μ / (16 + 35 * μ),
    225 * μ / (4 * (16 + 35 * μ)), 225 * μ / (8 * (16 + 35 * μ)), 15 * μ / (4 * (16 + 35 * μ)),
    15 * μ / (8 * (16 + 35 * μ))⟩, 0, 2 * (4 - 25 * μ ^ 2) / (5 * μ * (16 + 35 * μ))⟩

variable {μ : ℝ}

/-- The EMF at the point, `E* = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_emf (μ : ℝ) : (bpath μ).q.emf (bpath μ).Qf = 1 := by
  simp [bpath, emf]

/-- `|Z_t|² = 4500μ²/(16 + 35μ)²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_zsq (hμ : 0 < μ) :
    (bpath μ).q.ztsq = 4500 * μ ^ 2 / (16 + 35 * μ) ^ 2 := by
  have h : (16 + 35 * μ) ≠ 0 := by positivity
  simp only [ztsq, bpath]; field_simp; ring

/-- **The linear data are fixed along the path**: `P_tδ = 1/2`, `n_q P_tE = 2/5`, `Q_tδ = −1`,
`K_t = 6/5`, and the curvatures `P_tδδ = 7/8`, `Q_tδδ = 7/16`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_data (hμ : 0 < μ) :
    (bpath μ).q.Ptδ 0 1 = 1 / 2 ∧ (bpath μ).q.nq * (bpath μ).q.PtE 0 1 = 2 / 5 ∧
      (bpath μ).q.Qtδ 0 1 = -1 ∧ (bpath μ).q.gain 0 1 = 6 / 5 ∧
      (bpath μ).q.Ptδδ 0 1 = 7 / 8 ∧ (bpath μ).q.Qtδδ 0 1 = 7 / 16 := by
  have h : (16 + 35 * μ) ≠ 0 := by positivity
  have hμ0 : μ ≠ 0 := hμ.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Ptδ, PtE, Qtδ, QtE, gain, Ptδδ, Qtδδ, bpath_zsq hμ, Real.sin_zero,
      Real.cos_zero] <;>
    simp only [bpath] <;> field_simp <;> ring

/-- The selected point is balanced (`P_t = P_ref`, `Q_t = Q_f*`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_balance (hμ : 0 < μ) :
    (bpath μ).q.Pt 0 1 = (bpath μ).q.Pref ∧ (bpath μ).q.Qt 0 1 = (bpath μ).Qf := by
  have h : (16 + 35 * μ) ≠ 0 := by positivity
  have hμ0 : μ ≠ 0 := hμ.ne'
  refine ⟨?_, ?_⟩ <;> simp only [Pt_eq, Qt_eq, bpath_zsq hμ, Real.sin_zero, Real.cos_zero] <;>
    simp only [bpath] <;> field_simp <;> ring
/-- The Jacobian along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bpath_jacobian (hμ : 0 < μ) :
    (bpath μ).jacobian = !![0, 1, 0; -61 / 85, -4 / 17, 244 / 425; -1, 0, -6 / 5] := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := bpath_data hμ
  rw [Model.jacobian, bpath_emf, jacobian_eq_droopJacobian, show (bpath μ).δ = 0 from rfl, h1,
    h2, h3, h4]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [droopJacobian, bpath]

/-- **Every point of the path is a Hopf point** (`A = C = 1`, `G = 0`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bpath_isHopf (hμ : 0 < μ) : (bpath μ).IsHopf := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := bpath_data hμ
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
  obtain ⟨h1, -, -, h4, -, -⟩ := bpath_data hμ
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
    fnl μ x i = ![0, -(122 / 85) * ((16 * μ + 35 * μ ^ 2) / 80 * (x 2 * x 2) -
      7 / 8 * (Real.cos (x 0) - 1) + 1 / 2 * (Real.sin (x 0) - x 0) +
      7 * μ / 8 * ((Real.cos (x 0) - 1) * x 2) - μ / 2 * (Real.sin (x 0) * x 2)),
      (16 * μ + 35 * μ ^ 2) / 160 * (x 2 * x 2) - 7 / 16 * (Real.cos (x 0) - 1) -
      (Real.sin (x 0) - x 0) + 7 * μ / 16 * ((Real.cos (x 0) - 1) * x 2) +
      μ * (Real.sin (x 0) * x 2)] i := by
  have h : (16 + 35 * μ) ≠ 0 := by positivity
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hf : (bpath μ).field x = (bpath μ).q.field (x + (bpath μ).point) := rfl
  rw [fnl, PiLp.sub_apply, hf, A_apply hμ]
  fin_cases i
  · simp [Model.point]
  · simp only [Fin.mk_one, field_apply_one, Pt_eq, bpath_zsq hμ, emf, Model.point]
    simp [bpath]
    field_simp
    ring
  · simp only [Fin.reduceFinMk, field_apply_two, Qt_eq, bpath_zsq hμ, emf, Model.point]
    simp [bpath]
    field_simp
    ring

/-- The critical pair on the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCriticalPair_C (hμ : 0 < μ) :
    IsCriticalPair (bpath μ).field 0 1 qC pC := by
  have hM : 0 < (bpath μ).q.M := by norm_num [bpath]
  have hD : 0 < (bpath μ).q.D := by norm_num [bpath]
  have hω : 0 < (bpath μ).q.ωq := by norm_num [bpath]
  have hE : (bpath μ).q.emf (bpath μ).Qf ≠ 0 := by rw [bpath_emf]; norm_num
  obtain ⟨h1, -, h3, h4, -, -⟩ := bpath_data hμ
  have h := ((bpath μ).hopf_data hM hD hω hE (bpath_isHopf hμ)).1
  rw [bpath_hopfFreq hμ, bpath_emf, show (bpath μ).δ = 0 from rfl, h3, h4,
    show (bpath μ).q.ωq = 1 from rfl, show (bpath μ).q.M = 85 / 122 from rfl,
    show (bpath μ).q.D = 10 / 61 from rfl] at h
  exact h

/-- The critical data of the path at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem isCritical_C (hμ : 0 < μ) :
    IsCritical (fderiv ℝ (bpath μ).field 0) 1 qC pC :=
  IsCriticalPair.isCritical (isCriticalPair_C hμ) rfl

/-- `A w = −(122/85) w`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem A_wsv (hμ : 0 < μ) :
    fderiv ℝ (bpath μ).field 0 wsv = (-122 / 85 : ℝ) • wsv := by
  ext i; rw [A_apply hμ]; fin_cases i <;> simp [wsv] <;> norm_num

/-! ## The approximate centre manifold -/

/-- `h` of the manifold, degree 2. -/
def hL2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-13175275869 / 48401022800 + 64839767 / 605012785 * μ -
    91018039 / 1936040912 * μ ^ 2), 2, 0, 0), ((-5561737769 / 24200511400 + 124482334 / 605012785 *
    μ - 58788079 / 968020456 * μ ^ 2), 1, 1, 0), ((-7922898319 / 48401022800 + 78049317 / 605012785
    * μ - 254853669 / 1936040912 * μ ^ 2), 0, 2, 0)]

/-- `−(85/122) h`, the angle part of the manifold, degree 2. -/
def aL2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((3671798193 / 19360409120 - 18070099 / 242005114 * μ +
    126828415 / 3872081824 * μ ^ 2), 2, 0, 0), ((1549992493 / 9680204560 - 17345899 / 121002557 * μ
    + 81917815 / 1936040912 * μ ^ 2), 1, 1, 0), ((2208020843 / 19360409120 - 21751449 / 242005114 *
    μ + 355123965 / 3872081824 * μ ^ 2), 0, 2, 0)]

/-- `−(1445/488) h`, the `Q_f` part of the manifold, degree 2. -/
def cL2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((62420569281 / 77441636480 - 307191683 / 968020456 * μ +
    2156083055 / 15488327296 * μ ^ 2), 2, 0, 0), ((26349872381 / 38720818240 - 294880283 / 484010228
    * μ + 1392602855 / 7744163648 * μ ^ 2), 1, 1, 0), ((37536354331 / 77441636480 - 369774633 /
    968020456 * μ + 6037107405 / 15488327296 * μ ^ 2), 0, 2, 0)]

/-- `h` of the manifold, degree 3. -/
def hL3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-33200226251193346737 / 213776195273563117000 -
    18036858739340016149 / 85510478109425246800 * μ - 3443562639025856707 / 273633529950160789760 *
    μ ^ 2 - 51906126657946687 / 1710209562188504936 * μ ^ 3 - 608518591902507685 /
    54726705990032157952 * μ ^ 4), 3, 0, 0), ((-115410657280202850469 / 855104781094252468000 -
    33785885084293372947 / 85510478109425246800 * μ + 35501340396179991349 / 273633529950160789760 *
    μ ^ 2 - 9077218612307972 / 213776195273563117 * μ ^ 3 + 3250848806490886195 /
    54726705990032157952 * μ ^ 4), 2, 1, 0), ((-70511939237336142369 / 855104781094252468000 -
    18064594284201033597 / 85510478109425246800 * μ + 13959789885113509269 / 273633529950160789760 *
    μ ^ 2 - 4315527676770107 / 131554581706808072 * μ ^ 3 + 912373979274967195 /
    54726705990032157952 * μ ^ 4), 1, 2, 0), ((-6420780522970327481 / 106888097636781558500 -
    5869699181108509299 / 85510478109425246800 * μ + 26937044695747400713 / 273633529950160789760 *
    μ ^ 2 - 3667931702278627 / 65777290853404036 * μ ^ 3 + 6530671991411165815 /
    54726705990032157952 * μ ^ 4), 0, 3, 0)]

/-- `−(85/122) h`, the angle part of the manifold, degree 3. -/
def aL3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((9252522070004703189 / 85510478109425246800 +
    5026665550307873353 / 34204191243770098720 * μ + 959681391203927279 / 109453411980064315904 * μ
    ^ 2 + 72328209277466695 / 3420419124377009872 * μ ^ 3 + 847935742814969725 /
    109453411980064315904 * μ ^ 4), 3, 0, 0), ((32163625799400794393 / 342041912437700987200 +
    9415738466114546559 / 34204191243770098720 * μ - 9893816175984587753 / 109453411980064315904 * μ
    ^ 2 + 6324291656116210 / 213776195273563117 * μ ^ 3 - 4529871287733202075 /
    109453411980064315904 * μ ^ 4), 2, 1, 0), ((19650868312044498693 / 342041912437700987200 +
    5034395128383894609 / 34204191243770098720 * μ - 3890433246670977993 / 109453411980064315904 * μ
    ^ 2 + 6013440205335395 / 263109163413616144 * μ ^ 3 - 1271340790792987075 /
    109453411980064315904 * μ ^ 4), 1, 2, 0), ((1789397850663861757 / 42755239054712623400 +
    1635817804571223903 / 34204191243770098720 * μ - 7507045243077144461 / 109453411980064315904 * μ
    ^ 2 + 5111052372027595 / 131554581706808072 * μ ^ 3 - 9100116709343427775 /
    109453411980064315904 * μ ^ 4), 0, 3, 0)]

/-- `−(1445/488) h`, the `Q_f` part of the manifold, degree 3. -/
def cL3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((157292875190079954213 / 342041912437700987200 +
    85453314355233847001 / 136816764975080394880 * μ + 16314583650466763743 / 437813647920257263616
    * μ ^ 2 + 1229579557716933815 / 13681676497508039488 * μ ^ 3 + 14414907627854485325 /
    437813647920257263616 * μ ^ 4), 3, 0, 0), ((546781638589813504681 / 1368167649750803948800 +
    160067553923947291503 / 136816764975080394880 * μ - 168194874991737991801 /
    437813647920257263616 * μ ^ 2 + 53756479076987785 / 427552390547126234 * μ ^ 3 -
    77007811891464435275 / 437813647920257263616 * μ ^ 4), 2, 1, 0), ((334064761304756477781 /
    1368167649750803948800 + 85584717182526208353 / 136816764975080394880 * μ - 66137365193406625881
    / 437813647920257263616 * μ ^ 2 + 102228483490701715 / 1052436653654464576 * μ ^ 3 -
    21612793443480780275 / 437813647920257263616 * μ ^ 4), 1, 2, 0), ((30419763461285649869 /
    171020956218850493600 + 27808902677710806351 / 136816764975080394880 * μ - 127619769132311455837
    / 437813647920257263616 * μ ^ 2 + 86887890324469115 / 526218326827232288 * μ ^ 3 -
    154701984058838272175 / 437813647920257263616 * μ ^ 4), 0, 3, 0)]

/-- `h` of the manifold, degree 4. -/
def hL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-47358603572283627184873212796230662803 /
    70936184540382520066204088305764510720000 + 10977587575809729524620353568291657381 /
    115343389496556943197079818383356928000 * μ - 221634474698206921632017126286116277197 /
    15133052701948270947456872171896428953600 * μ ^ 2 + 1572421950198744352725683783751387157 /
    47290789693588346710802725537176340480 * μ ^ 3 - 25956089551917067919801935461558480223 /
    302661054038965418949137443437928579072 * μ ^ 4 - 730676379640277114577119754402774525 /
    37832631754870677368642180429741072384 * μ ^ 5 - 16267472792668022470395970840644202125 /
    605322108077930837898274886875857158144 * μ ^ 6), 4, 0, 0),
    ((-1238258521919856963632863792217847793303 / 17734046135095630016551022076441127680000 +
    368571340076002483847729831955809106713 / 3546809227019126003310204415288225536000 * μ +
    16805040227466394522157206815505024009 / 276824134791736663672991564120056627200 * μ ^ 2 +
    904822018573880952373837729469118907 / 11822697423397086677700681384294085120 * μ ^ 3 +
    1819040287029696599624976302510652917 / 75665263509741354737284360859482144768 * μ ^ 4 +
    15005052893433699733192752825133925 / 9458157938717669342160545107435268096 * μ ^ 5 +
    4113387406023574624784424224130205875 / 151330527019482709474568721718964289536 * μ ^ 6), 3, 1,
    0), ((-116317872804992391427384288741447561 / 2160185898665647118162010119549440000 +
    123008261845731472224619885283760231 / 432037179733129423632402023909888000 * μ +
    299490547524100054946111032016078023 / 1382518975146014155623686476511641600 * μ ^ 2 +
    83518869230720115508904002521547 / 270023237333205889770251264943680 * μ ^ 3 -
    17343019342145428264491919831763 / 65677861052067180789723823112192 * μ ^ 4 -
    134318121452541090006607669375 / 265869033681925799158401245483008 * μ ^ 5 -
    6644506703678717686294869157738625 / 55300759005840566224947459060465664 * μ ^ 6), 2, 2, 0),
    ((-370386430293319893330912411663365630453 / 17734046135095630016551022076441127680000 +
    142729122637856200199300086257706027421 / 1182269742339708667770068138429408512000 * μ +
    731603570628269328266155566278520483813 / 3783263175487067736864218042974107238400 * μ ^ 2 +
    1209559409097290858619327525798630007 / 11822697423397086677700681384294085120 * μ ^ 3 -
    2494820142130360353055432576366712453 / 75665263509741354737284360859482144768 * μ ^ 4 -
    446202201193037398449842629250376925 / 9458157938717669342160545107435268096 * μ ^ 5 +
    2048563010590806121687202686146898125 / 151330527019482709474568721718964289536 * μ ^ 6), 1, 3,
    0), ((-1049418596946234660688568242612798481603 / 70936184540382520066204088305764510720000 +
    1213611626220029089137016944595023214963 / 14187236908076504013240817661152902144000 * μ +
    10243616528670037222546211628991701138049 / 45399158105844812842370616515689286860800 * μ ^ 2 +
    3998071839345519749868829544808718107 / 47290789693588346710802725537176340480 * μ ^ 3 -
    53705850664605105736445111094578732463 / 302661054038965418949137443437928579072 * μ ^ 4 +
    52616835197620223080185496370388775 / 37832631754870677368642180429741072384 * μ ^ 5 -
    91722989003766277867896974737137705125 / 605322108077930837898274886875857158144 * μ ^ 6), 0, 4,
    0)]

/-- `−(85/122) h`, the angle part of the manifold, degree 4. -/
def aL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((13198299356210191182669583894031496191 /
    28374473816153008026481635322305804288000 - 3059327685061727900304032961655052057 /
    46137355798622777278831927353342771200 * μ + 61766984751959306028594936833835683809 /
    6053221080779308378982748868758571581440 * μ ^ 2 - 26731173153378653996336624323773581669 /
    1153895268523555659743586503107102707712 * μ ^ 3 + 2206267611912950773183164514232470818955 /
    36924648592753781111794768099427286646784 * μ ^ 4 + 62107492269423554739055179124235834625 /
    4615581074094222638974346012428410830848 * μ ^ 5 + 1382735187376781909983657521454757180625 /
    73849297185507562223589536198854573293568 * μ ^ 6), 4, 0, 0),
    ((345088440535042104618994827339400204691 / 7093618454038252006620408830576451072000 -
    102716602972000692219859133495881226461 / 1418723690807650401324081766115290214400 * μ -
    4683371866670962407814303538747301773 / 110729653916694665469196625648022650880 * μ ^ 2 -
    252163513373048790005823629524180679 / 4729078969358834671080272553717634048 * μ ^ 3 -
    2534728268811872310952835831367303245 / 151330527019482709474568721718964289536 * μ ^ 4 -
    20908680261342040611825967051416125 / 18916315877435338684321090214870536192 * μ ^ 5 -
    5731769336262358083716000968050286875 / 302661054038965418949137443437928579072 * μ ^ 6), 3, 1,
    0), ((32416456355489682856812014895157517 / 864074359466258847264804047819776000 -
    34280991006187459472435049997113507 / 172814871893251769452960809563955200 * μ -
    83464578818191818591539140070054531 / 553007590058405662249474590604656640 * μ ^ 2 -
    1419820776922241963651368042866299 / 6588566990930223710394130864625792 * μ ^ 3 +
    1474156644082361402481813185699855 / 8012699048352196056346306419687424 * μ ^ 4 +
    11417040323465992650561651896875 / 32436022109194947497324951948926976 * μ ^ 5 +
    564783069812691003335063878407783125 / 6746692598712549079443590005376811008 * μ ^ 6), 2, 2, 0),
    ((103222447786662921092221491775036323241 / 7093618454038252006620408830576451072000 -
    39776968603992711530952483055426269937 / 472907896935883467108027255371763404800 * μ -
    203889519683288173451223682405489315161 / 1513305270194827094745687217189642895360 * μ ^ 2 -
    337090327125474501582435539976667379 / 4729078969358834671080272553717634048 * μ ^ 3 +
    3476388722640666065732979819527386205 / 151330527019482709474568721718964289536 * μ ^ 4 +
    621757165596855391282567598135771125 / 18916315877435338684321090214870536192 * μ ^ 5 -
    2854555014757680661367413579057153125 / 302661054038965418949137443437928579072 * μ ^ 6), 1, 3,
    0), ((292460920460426052978781313515042199791 / 28374473816153008026481635322305804288000 -
    338219633536729418284086689477301551711 / 5674894763230601605296327064461160857600 * μ -
    2854778376842469389889927831030474087653 / 18159663242337925136948246606275714744320 * μ ^ 2 -
    67967221268873835747770102261748207819 / 1153895268523555659743586503107102707712 * μ ^ 3 +
    4564997306491433987597834443039192259355 / 36924648592753781111794768099427286646784 * μ ^ 4 -
    4472430991797718961815767191483045875 / 4615581074094222638974346012428410830848 * μ ^ 5 +
    7796454065320133618771242852656704935625 / 73849297185507562223589536198854573293568 * μ ^ 6),
    0, 4, 0)]

/-- `−(1445/488) h`, the `Q_f` part of the manifold, degree 4. -/
def cL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((224371089055573250105382926198535435247 /
    113497895264612032105926541289223217152000 - 52008570646049374305168560348135884969 /
    184549423194491109115327709413371084800 * μ + 1050038740783308202486113926175206624753 /
    24212884323117233515930995475034286325760 * μ ^ 2 - 454429943607437117937722613504150888373 /
    4615581074094222638974346012428410830848 * μ ^ 3 + 37506549402520163144113796741952003922235 /
    147698594371015124447179072397709146587136 * μ ^ 4 + 1055827368580200430563938045112009188625 /
    18462324296376890555897384049713643323392 * μ ^ 5 + 23506498185405292469722177864730872070625 /
    295397188742030248894358144795418293174272 * μ ^ 6), 4, 0, 0),
    ((5866503489095715778522912064769803479747 / 28374473816153008026481635322305804288000 -
    1746182250524011767737605269429980849837 / 5674894763230601605296327064461160857600 * μ -
    79617321733406360932843160158704130141 / 442918615666778661876786502592090603520 * μ ^ 2 -
    4286779727341829430099001701911071543 / 18916315877435338684321090214870536192 * μ ^ 3 -
    43090380569801829286198209133244155165 / 605322108077930837898274886875857158144 * μ ^ 4 -
    355447564442814690401041439874074125 / 75665263509741354737284360859482144768 * μ ^ 5 -
    97440078716460087423172016456854876875 / 1210644216155861675796549773751714316288 * μ ^ 6), 3,
    1, 0), ((551079758043324608565804253217677789 / 3456297437865035389059216191279104000 -
    582776847105186811031395849950929619 / 691259487573007077811843238255820800 * μ -
    1418897839909260916056165381190927027 / 2212030360233622648997898362418626560 * μ ^ 2 -
    24136953207678113382073256728727083 / 26354267963720894841576523458503168 * μ ^ 3 +
    25060662949400143842190824156897535 / 32050796193408784225385225678749696 * μ ^ 4 +
    194089685498921875059548082246875 / 129744088436779789989299807795707904 * μ ^ 5 +
    9601312186815747056696085932932313125 / 26986770394850196317774360021507244032 * μ ^ 6), 2, 2,
    0), ((1754781612373269658567765360175617495097 / 28374473816153008026481635322305804288000 -
    676208466267876096026192211942246588929 / 1891631587743533868432109021487053619200 * μ -
    3466121834615898948670802600893318357737 / 6053221080779308378982748868758571581440 * μ ^ 2 -
    5730535561133066526901404179603345443 / 18916315877435338684321090214870536192 * μ ^ 3 +
    59098608284891323117460656931965565485 / 605322108077930837898274886875857158144 * μ ^ 4 +
    10569871815146541651803649168308109125 / 75665263509741354737284360859482144768 * μ ^ 5 -
    48527435250880571243246030843971603125 / 1210644216155861675796549773751714316288 * μ ^ 6), 1,
    3, 0), ((4971835647827242900639282329755717396447 / 113497895264612032105926541289223217152000 -
    5749733770124400110829473721114126379087 / 22699579052922406421185308257844643430400 * μ -
    48531232406321979628128773127518059490101 / 72638652969351700547792986425102858977280 * μ ^ 2 -
    1155442761570855207712091738449719532923 / 4615581074094222638974346012428410830848 * μ ^ 3 +
    77604954210354377789163185531666268409035 / 147698594371015124447179072397709146587136 * μ ^ 4 -
    76031326860561222350868042255211779875 / 18462324296376890555897384049713643323392 * μ ^ 5 +
    132539719110442271519111128495163983905625 / 295397188742030248894358144795418293174272 * μ ^
    6), 0, 4, 0)]

/-- The weight-five truncation of `cos x₀ − 1`, degrees two to four. -/
def low2L4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-121 / 50), 2, 0, 0), ((-11 / 25), 1, 1, 0), ((-1 /
    50), 0, 2, 0), ((-40389780123 / 96802045600 + 198771089 / 1210025570 * μ - 279022513 /
    3872081824 * μ ^ 2), 3, 0, 0), ((-37771633039 / 96802045600 + 399679877 / 1210025570 * μ -
    385804069 / 3872081824 * μ ^ 2), 2, 1, 0), ((-27388214259 / 96802045600 + 273957737 / 1210025570
    * μ - 814039849 / 3872081824 * μ ^ 2), 1, 2, 0), ((-2208020843 / 96802045600 + 21751449 /
    1210025570 * μ - 71024793 / 3872081824 * μ ^ 2), 0, 3, 0), ((3234964111294223716713824521 /
    4492788928251690007069440000 - 578730978647526622795003 / 1871995386771537502945600 * μ -
    169463328599730426622389 / 5990385237668920009425920 * μ ^ 2 - 3300364539283385892003 /
    74879815470861500117824 * μ ^ 3 - 42123992392201197370865 / 2396154095067568003770368 * μ ^ 4),
    4, 0, 0), ((107883065345165165873792861 / 1123197232062922501767360000 -
    139432175797157747170079 / 233999423346442187868200 * μ + 259290437449369755424681 /
    1497596309417230002356480 * μ ^ 2 - 575250764689757045449 / 9359976933857687514728 * μ ^ 3 +
    52784002677162009946735 / 599038523766892000942592 * μ ^ 4), 3, 1, 0),
    ((-98279334407700984572715449 / 748798154708615001178240000 - 309207711736280770174839 /
    935997693385768751472800 * μ + 153908537668499108085753 / 2995192618834460004712960 * μ ^ 2 -
    1510356287649355285629 / 37439907735430750058912 * μ ^ 3 + 35860656698138369800255 /
    1198077047533784001885184 * μ ^ 4), 2, 2, 0), ((-133540362842137107979671409 /
    1123197232062922501767360000 - 12157659354006479349967 / 116999711673221093934100 * μ +
    188104432781857003346821 / 1497596309417230002356480 * μ ^ 2 - 684151972499535522969 /
    9359976933857687514728 * μ ^ 3 + 108637843817880853339185 / 599038523766892000942592 * μ ^ 4),
    1, 3, 0), ((-66525900528720758425223519 / 4492788928251690007069440000 + 1283546832139345522077
    / 1871995386771537502945600 * μ - 4682689562396745740609 / 5990385237668920009425920 * μ ^ 2 +
    35419914788179478417 / 74879815470861500117824 * μ ^ 3 + 29766384844580642401535 /
    2396154095067568003770368 * μ ^ 4), 0, 4, 0)]

/-- The weight-five truncation of `cos x₀ − 1`, degree five. -/
def low2L5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((44694017788150256400831647419893148136747 /
    141872369080765040132408176611529021440000 - 182266912274113651698588878937234448783 /
    28374473816153008026481635322305804288000 * μ + 3763221249817743595184186538869508171311 /
    90798316211689625684741233031378573721600 * μ ^ 2 + 246909809279979937170185751045956524039 /
    5769476342617778298717932515535513538560 * μ ^ 3 - 4860343327767930948907115775953608450741 /
    36924648592753781111794768099427286646784 * μ ^ 4 - 137163460249069272032835896592119083775 /
    4615581074094222638974346012428410830848 * μ ^ 5 - 3060756655250845495457651836836744659375 /
    73849297185507562223589536198854573293568 * μ ^ 6), 5, 0, 0),
    ((6630396987855481218668647747664104812961 / 28374473816153008026481635322305804288000 -
    323855403259718034153255704215249443007 / 1891631587743533868432109021487053619200 * μ +
    280452128528918710672920840252892205947 / 1210644216155861675796549773751714316288 * μ ^ 2 +
    106409152500975215980150593871042318261 / 1153895268523555659743586503107102707712 * μ ^ 3 +
    1452533945210044153633637395678555871325 / 36924648592753781111794768099427286646784 * μ ^ 4 -
    18937383058067338712244170731695301025 / 4615581074094222638974346012428410830848 * μ ^ 5 +
    2876169006748139933414567704543624708375 / 73849297185507562223589536198854573293568 * μ ^ 6),
    4, 1, 0), ((149139040034426712964504298207122889339 / 945815793871766934216054510743526809600 +
    446777702048570215756580700498720429961 / 2837447381615300802648163532230580428800 * μ +
    5386836997980401927243878437142059225049 / 9079831621168962568474123303137857372160 * μ ^ 2 +
    123612490005006062168952229692505077799 / 288473817130888914935896625776775676928 * μ ^ 3 -
    7041930653405269035960741639669844770795 / 18462324296376890555897384049713643323392 * μ ^ 4 -
    24455279746834263789597053084260899175 / 2307790537047111319487173006214205415424 * μ ^ 5 -
    6607998753501784674260134729892263785125 / 36924648592753781111794768099427286646784 * μ ^ 6),
    3, 2, 0), ((-69232316979149634096936707496131197781 / 14187236908076504013240817661152902144000
    + 370540783720888005537018276766385812063 / 2837447381615300802648163532230580428800 * μ +
    3984996066547729625044377932748209336143 / 9079831621168962568474123303137857372160 * μ ^ 2 +
    38693571698523170293056873503067507825 / 288473817130888914935896625776775676928 * μ ^ 3 -
    814357020687050222927049766422280607565 / 18462324296376890555897384049713643323392 * μ ^ 4 -
    205226233452907514534847525393374275825 / 2307790537047111319487173006214205415424 * μ ^ 5 +
    406808840180475279619570169048356860125 / 36924648592753781111794768099427286646784 * μ ^ 6), 2,
    3, 0), ((-953611952956162750534284209843571723037 / 28374473816153008026481635322305804288000 +
    49376905347069306591008897546575454579 / 378326317548706773686421804297410723840 * μ +
    2451363851862065893060953329511135598429 / 6053221080779308378982748868758571581440 * μ ^ 2 +
    2996316500867902032242450244797492537 / 28143787037159894140087475685539090432 * μ ^ 3 -
    9163137690424981578457317202638768148985 / 36924648592753781111794768099427286646784 * μ ^ 4 -
    97593993069569484138065895386325855975 / 4615581074094222638974346012428410830848 * μ ^ 5 -
    16674432445664945324963428531533544655875 / 73849297185507562223589536198854573293568 * μ ^ 6),
    1, 4, 0), ((-316022349926310216026716503387866229861 / 47290789693588346710802725537176340480000
    + 286790015602614676797742804234296943727 / 28374473816153008026481635322305804288000 * μ +
    3617899515407130398711046384404065465781 / 90798316211689625684741233031378573721600 * μ ^ 2 -
    18469432279904916742876428059567747701 / 5769476342617778298717932515535513538560 * μ ^ 3 -
    4918698599668998053616958288417295671 / 900601185189116612482799221937250893824 * μ ^ 4 -
    50042888781173171697113866878089510425 / 4615581074094222638974346012428410830848 * μ ^ 5 -
    996172722927628097469420899169662189125 / 73849297185507562223589536198854573293568 * μ ^ 6), 0,
    5, 0)]

/-- The weight-five truncation of `sin x₀ − x₀`, degrees two to four. -/
def low3L4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-1331 / 750), 3, 0, 0), ((-121 / 250), 2, 1, 0),
    ((-11 / 250), 1, 2, 0), ((-1 / 750), 0, 3, 0), ((-444287581353 / 968020456000 + 2186481979 /
    12100255700 * μ - 3069247643 / 38720818240 * μ ^ 2), 4, 0, 0), ((-7123089743 / 15125319625 +
    1148812434 / 3025063925 * μ - 565358409 / 4840102280 * μ ^ 2), 3, 1, 0), ((-5297531092 /
    15125319625 + 853303746 / 3025063925 * μ - 1167530301 / 4840102280 * μ ^ 2), 2, 2, 0),
    ((-12919110883 / 242005114000 + 128305919 / 3025063925 * μ - 398828143 / 9680204560 * μ ^ 2), 1,
    3, 0), ((-2208020843 / 968020456000 + 21751449 / 12100255700 * μ - 71024793 / 38720818240 * μ ^
    2), 0, 4, 0)]

/-- The weight-five truncation of `sin x₀ − x₀`, degree five. -/
def low3L5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((14382681689148895245062557871 /
    112319723206292250176736000000 - 379652119718219869570973 / 1169997116732210939341000 * μ -
    76785245490992769943267 / 1871995386771537502945600 * μ ^ 2 - 17144759126339404080059 /
    374399077354307500589120 * μ ^ 3 - 47750300801115766544229 / 2396154095067568003770368 * μ ^ 4),
    5, 0, 0), ((-3377774804030593010370227339 / 22463944641258450035347200000 -
    600810902491660406341439 / 935997693385768751472800 * μ + 6003569686363796723233 /
    37439907735430750058912 * μ ^ 2 - 4726948402625236983979 / 74879815470861500117824 * μ ^ 3 +
    224255728965382058855085 / 2396154095067568003770368 * μ ^ 4), 4, 1, 0),
    ((-2571448069105345523878170199 / 11231972320629225017673600000 - 342286212921256415876127 /
    935997693385768751472800 * μ + 66075380403025645135717 / 2995192618834460004712960 * μ ^ 2 -
    1209006205171779280609 / 37439907735430750058912 * μ ^ 3 + 44698775572385625164215 /
    1198077047533784001885184 * μ ^ 4), 3, 2, 0), ((-1935041257058955222211509209 /
    11231972320629225017673600000 - 101716722114985045937981 / 935997693385768751472800 * μ +
    309041866385017033059289 / 2995192618834460004712960 * μ ^ 2 - 2403852319042644899149 /
    37439907735430750058912 * μ ^ 3 + 237007978794599011755245 / 1198077047533784001885184 * μ ^ 4),
    2, 3, 0), ((-839641259956608466364035369 / 22463944641258450035347200000 + 882239772085539432061
    / 187199538677153750294560 * μ - 22427748475591310828627 / 2995192618834460004712960 * μ ^ 2 +
    297543530673508232701 / 74879815470861500117824 * μ ^ 3 + 64182985660124913319675 /
    2396154095067568003770368 * μ ^ 4), 1, 4, 0), ((-239811185098977748325817179 /
    112319723206292250176736000000 + 2559094419139413485799 / 2339994233464421878682000 * μ -
    22884374088878978687831 / 14975963094172300023564800 * μ ^ 2 + 326336926962092563741 /
    374399077354307500589120 * μ ^ 3 + 1968881868897202063301 / 2396154095067568003770368 * μ ^ 4),
    0, 5, 0)]

/-- The weight-five truncation of `(cos x₀ − 1) x₂`, degrees two to four. -/
def lowCL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((121 / 50), 3, 0, 0), ((143 / 50), 2, 1, 0), ((23 /
    50), 1, 2, 0), ((1 / 50), 0, 3, 0), ((-5937297678081 / 3872081824000 + 29219350083 / 48401022800
    * μ - 41016309411 / 154883272960 * μ ^ 2), 4, 0, 0), ((-22228197663 / 18615778000 + 520973143 /
    465394450 * μ - 483612311 / 1489262240 * μ ^ 2), 3, 1, 0), ((-197332496011 / 242005114000 +
    3884893771 / 6050127850 * μ - 13848795527 / 19360409120 * μ ^ 2), 2, 2, 0), ((76337466009 /
    968020456000 - 775891237 / 12100255700 * μ + 2070567989 / 38720818240 * μ ^ 2), 1, 3, 0),
    ((50784479389 / 3872081824000 - 500283327 / 48401022800 * μ + 1633570239 / 154883272960 * μ ^
    2), 0, 4, 0)]

/-- The weight-five truncation of `(cos x₀ − 1) x₂`, degree five. -/
def lowCL5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-19491665661856771747118527931 /
    8985577856503380014138880000 - 35100752264995695866391363 / 37439907735430750058912000 * μ -
    27577851300505901962871349 / 119807704753378400188518400 * μ ^ 2 - 47801813952912182109597 /
    374399077354307500589120 * μ ^ 3 - 172833013954943630650467 / 2396154095067568003770368 * μ ^
    4), 5, 0, 0), ((-1547923158528234400214568463 / 599038523766892000942592000 -
    10820166188139018575413591 / 7487981547086150011782400 * μ + 1460932166150190984051957 /
    4792308190135136007540736 * μ ^ 2 - 13064308838971248564699 / 149759630941723000235648 * μ ^ 3 +
    751932219399686253743605 / 2396154095067568003770368 * μ ^ 4), 4, 1, 0),
    ((-1290825740309181345349260577 / 898557785650338001413888000 - 132051297376546002052451 /
    935997693385768751472800 * μ - 3419733766586113776556943 / 5990385237668920009425920 * μ ^ 2 +
    2237107059967421757409 / 18719953867715375029456 * μ ^ 3 + 6901563633370313216365 /
    2396154095067568003770368 * μ ^ 4), 3, 2, 0), ((-125040662122874589982770719 /
    179711557130067600282777600 + 140900127128898289645731 / 467998846692884375736400 * μ -
    238208756862196147731903 / 2995192618834460004712960 * μ ^ 2 + 937867451676710930361 /
    74879815470861500117824 * μ ^ 3 + 1413412295418895503255545 / 2396154095067568003770368 * μ ^
    4), 2, 3, 0), ((-61165659625074226702512681 / 599038523766892000942592000 +
    367254062485484672154643 / 1497596309417230002356480 * μ - 7661658206970055729924643 /
    23961540950675680037703680 * μ ^ 2 + 13552533091022698105263 / 74879815470861500117824 * μ ^ 3 -
    9177158132097978710625 / 74879815470861500117824 * μ ^ 4), 1, 4, 0), ((1742096253390246161313979
    / 8985577856503380014138880000 + 474564028715284566786147 / 37439907735430750058912000 * μ -
    2160946643256976233756229 / 119807704753378400188518400 * μ ^ 2 + 7666323213952040024681 /
    748798154708615001178240 * μ ^ 3 - 3745571016754357766969 / 299519261883446000471296 * μ ^ 4),
    0, 5, 0)]

/-- The weight-five truncation of `sin x₀ · x₂`, degrees two to four. -/
def lowSL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-11 / 5), 2, 0, 0), ((-12 / 5), 1, 1, 0), ((-1 / 5),
    0, 2, 0), ((613190298231 / 387208182400 - 3017706533 / 4840102280 * μ + 4236069061 / 15488327296
    * μ ^ 2), 3, 0, 0), ((1203520423 / 919734400 - 13632589 / 11496680 * μ + 12817133 / 36789376 * μ
    ^ 2), 2, 1, 0), ((359439525823 / 387208182400 - 3528416589 / 4840102280 * μ + 11762839053 /
    15488327296 * μ ^ 2), 1, 2, 0), ((-6624062529 / 387208182400 + 65254347 / 4840102280 * μ -
    213074379 / 15488327296 * μ ^ 2), 0, 3, 0), ((5087693733211973339497978171 /
    1797115571300676002827776000 + 1035915485435777369823617 / 935997693385768751472800 * μ +
    448410745401296198750361 / 2995192618834460004712960 * μ ^ 2 + 23329627607519931804393 /
    149759630941723000235648 * μ ^ 3 + 331853578536120288856915 / 4792308190135136007540736 * μ ^
    4), 4, 0, 0), ((1476216040557095500417008691 / 449278892825169000706944000 +
    3638838713213130948285821 / 1871995386771537502945600 * μ - 827159126275806818870513 /
    1497596309417230002356480 * μ ^ 2 + 13260194387372953370301 / 74879815470861500117824 * μ ^ 3 -
    401304728051620617923685 / 1198077047533784001885184 * μ ^ 4), 3, 1, 0),
    ((385311321533323677796670261 / 299519261883446000471296000 + 725711031153589491955917 /
    935997693385768751472800 * μ + 589066004321674839341137 / 5990385237668920009425920 * μ ^ 2 +
    483111876541118027903 / 9359976933857687514728 * μ ^ 3 - 138107277413285299901355 /
    2396154095067568003770368 * μ ^ 4), 2, 2, 0), ((243240781251322655672058881 /
    449278892825169000706944000 + 217088655801152748901141 / 1871995386771537502945600 * μ -
    874617668225596426141841 / 2995192618834460004712960 * μ ^ 2 + 13246331466914791891331 /
    74879815470861500117824 * μ ^ 3 - 790136334626440228798385 / 1198077047533784001885184 * μ ^ 4),
    1, 3, 0), ((90458317386725317903898051 / 1797115571300676002827776000 - 44134379673730785682089
    / 467998846692884375736400 * μ + 799894945664554754043657 / 5990385237668920009425920 * μ ^ 2 -
    11366068001833835290077 / 149759630941723000235648 * μ ^ 3 + 231084551145630466320015 /
    4792308190135136007540736 * μ ^ 4), 0, 4, 0)]

/-- The weight-five truncation of `sin x₀ · x₂`, degree five. -/
def lowSL5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-450110502946207854166188998424023773615079 /
    567489476323060160529632706446116085760000 - 337064701282942252804281126026820788629 /
    113497895264612032105926541289223217152000 * μ - 47792482294681490381948783631574328542987 /
    363193264846758502738964932125514294886400 * μ ^ 2 - 2861580672769936486544634300541390411843 /
    23077905370471113194871730062142054154240 * μ ^ 3 + 73912194010913490253058925493198395420457 /
    147698594371015124447179072397709146587136 * μ ^ 4 + 2092307468514220082919536068388685294875 /
    18462324296376890555897384049713643323392 * μ ^ 5 + 46820489521129975772236741064222371140875 /
    295397188742030248894358144795418293174272 * μ ^ 6), 5, 0, 0),
    ((3334025231286891197186002668472022101 / 89863733384490920115539620973256704000 +
    28684299677851398110903422374126672037 / 53918240030694552069323772583954022400 * μ -
    33389884753791255732674751371279711257 / 34507673619644513324367214453730574336 * μ ^ 2 -
    2073267356315832889856059847073754797 / 10963375472907892254095833758737317888 * μ ^ 3 -
    95267751508473462253629269416273713125 / 350828015133052552131066680279594172416 * μ ^ 4 +
    939398350851610376702410138063848425 / 43853501891631569016383335034949271552 * μ ^ 5 -
    119054502348781727913322594380977827375 / 701656030266105104262133360559188344832 * μ ^ 6), 4,
    1, 0), ((2583329639904073003442106273279465780607 / 11349789526461203210592654128922321715200 -
    3026315653565373296404119044728300349919 / 3783263175487067736864218042974107238400 * μ -
    27355179828784901366290182702894965426511 / 12106442161558616757965497737517143162880 * μ ^ 2 -
    1515349128307605385484170989879234820443 / 1153895268523555659743586503107102707712 * μ ^ 3 +
    101092561905766367454069850771677933947015 / 73849297185507562223589536198854573293568 * μ ^ 4 +
    816726192450569291991331113727323611475 / 9231162148188445277948692024856821661696 * μ ^ 5 +
    101876808494925220346957275780124770099625 / 147698594371015124447179072397709146587136 * μ ^
    6), 3, 2, 0), ((27847160308385571090686900195695632478637 /
    56748947632306016052963270644611608576000 - 4642985780145677297752012800891856804931 /
    11349789526461203210592654128922321715200 * μ - 57299431386386682985732281147658347687731 /
    36319326484675850273896493212551429488640 * μ ^ 2 - 4269322191065011857465898369670005045 /
    1153895268523555659743586503107102707712 * μ ^ 3 - 15005637440869503413130687105556995192295 /
    73849297185507562223589536198854573293568 * μ ^ 4 + 3831309743987648597752721837526572960525 /
    9231162148188445277948692024856821661696 * μ ^ 5 - 22287541381626014195901607330833162359625 /
    147698594371015124447179072397709146587136 * μ ^ 6), 2, 3, 0),
    ((8700302674872903849772187956268894378723 / 37832631754870677368642180429741072384000 -
    1810257955784685510960874835141889757949 / 4539915810584481284237061651568928686080 * μ -
    109356712343945414502395052139888838408179 / 72638652969351700547792986425102858977280 * μ ^ 2 -
    754371947020721872931047796629458173349 / 4615581074094222638974346012428410830848 * μ ^ 3 +
    116278825508104019932710970585756908996445 / 147698594371015124447179072397709146587136 * μ ^ 4
    + 2380709669224105931213609149668528859075 / 18462324296376890555897384049713643323392 * μ ^ 5 +
    249311689383001077433792117930498529647375 / 295397188742030248894358144795418293174272 * μ ^
    6), 1, 4, 0), ((23074402679428381371013021409738190666931 /
    567489476323060160529632706446116085760000 + 833811664161409457036227307629867367167 /
    37832631754870677368642180429741072384000 * μ - 5508943217838970924952838095186672465659 /
    121064421615586167579654977375171431628800 * μ ^ 2 + 3142747884465099091925292337709987111137 /
    23077905370471113194871730062142054154240 * μ ^ 3 - 26924314220098028221481935024436312553853 /
    147698594371015124447179072397709146587136 * μ ^ 4 + 1734554207899190958019308151072017893925 /
    18462324296376890555897384049713643323392 * μ ^ 5 - 23823887503829633464946886537891102093375 /
    295397188742030248894358144795418293174272 * μ ^ 6), 0, 5, 0)]

/-- The weight-five truncation of `x₂²`, degrees two to four. -/
def lowQL4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((1), 2, 0, 0), ((2), 1, 1, 0), ((1), 0, 2, 0),
    ((-62420569281 / 38720818240 + 307191683 / 484010228 * μ - 2156083055 / 7744163648 * μ ^ 2), 3,
    0, 0), ((-115120314043 / 38720818240 + 896952249 / 484010228 * μ - 4941288765 / 7744163648 * μ ^
    2), 2, 1, 0), ((-90236099093 / 38720818240 + 959535199 / 484010228 * μ - 8822313115 / 7744163648
    * μ ^ 2), 1, 2, 0), ((-37536354331 / 38720818240 + 369774633 / 484010228 * μ - 6037107405 /
    7744163648 * μ ^ 2), 0, 3, 0), ((-129410688079219952217870939 / 479230819013513600754073600 -
    5273749361973894338348791 / 2995192618834460004712960 * μ + 2401791881850837947235735 /
    9584616380270272015081472 * μ ^ 2 - 160598013197220841439505 / 599038523766892000942592 * μ ^ 3
    - 890812131118056219044875 / 19169232760540544030162944 * μ ^ 4), 4, 0, 0),
    ((-74519480690067273577577039 / 119807704753378400188518400 - 3746307897226790348689341 /
    748798154708615001178240 * μ + 3737623167222599126907585 / 2396154095067568003770368 * μ ^ 2 -
    107071637405339364974405 / 149759630941723000235648 * μ ^ 3 + 1610216019944719865201125 /
    4792308190135136007540736 * μ ^ 4), 3, 1, 0), ((-10341639944835820354603967 /
    239615409506756800377036800 - 8002535714668211425505223 / 1497596309417230002356480 * μ +
    12901562306626637354876255 / 4792308190135136007540736 * μ ^ 2 - 305086536711479573957165 /
    299519261883446000471296 * μ ^ 3 + 5668082353710288675627625 / 9584616380270272015081472 * μ ^
    4), 2, 2, 0), ((-22091285994038444570952789 / 119807704753378400188518400 -
    2072749412922378679448491 / 748798154708615001178240 * μ + 4925036070857279095681735 /
    2396154095067568003770368 * μ ^ 2 - 170252205167180070123455 / 149759630941723000235648 * μ ^ 3
    + 4531701486068598835879375 / 4792308190135136007540736 * μ ^ 4), 1, 3, 0),
    ((-57893047465370634613387939 / 479230819013513600754073600 - 2326721247353300569929591 /
    2995192618834460004712960 * μ + 10607911804331412751186535 / 9584616380270272015081472 * μ ^ 2 -
    376209956688566530600105 / 599038523766892000942592 * μ ^ 3 + 16459359959035241508924125 /
    19169232760540544030162944 * μ ^ 4), 0, 4, 0)]

/-- The weight-five truncation of `x₂²`, degree five. -/
def lowQL5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((41845456900083779862166047230562920978729 /
    56748947632306016052963270644611608576000 + 193495659558889393714104414515953270637 /
    151330527019482709474568721718964289536 * μ - 3571878216215781266855775271115751070501 /
    12106442161558616757965497737517143162880 * μ ^ 2 + 1135503172241264078546244947153889922297 /
    2307790537047111319487173006214205415424 * μ ^ 3 - 37032980884850677483038681466555030029095 /
    73849297185507562223589536198854573293568 * μ ^ 4 - 1017753261809819551964365238128691299525 /
    9231162148188445277948692024856821661696 * μ ^ 5 - 22152587877071190014809195688509724291125 /
    147698594371015124447179072397709146587136 * μ ^ 6), 5, 0, 0),
    ((9677731142960402537940749733167979098519 / 11349789526461203210592654128922321715200 +
    1407891159967781218569028601625909689339 / 453991581058448128423706165156892868608 * μ -
    269779801939180716561883203008567467903 / 177167446266711464750714601036836241408 * μ ^ 2 +
    97035796363594033082705495751368090825 / 56287574074319788280174951371078180864 * μ ^ 3 -
    65512246845110452237275868465292079505675 / 73849297185507562223589536198854573293568 * μ ^ 4 +
    312592573315878644555146004165755295375 / 9231162148188445277948692024856821661696 * μ ^ 5 -
    5215057590004596479709935342887692450625 / 147698594371015124447179072397709146587136 * μ ^ 6),
    4, 1, 0), ((14429951374514579277311461387627647359 / 22167557668869537520688777595551409600 +
    1024768195522779208910236182573181794535 / 226995790529224064211853082578446434304 * μ -
    2968727520128335768190015332892477592253 / 3631932648467585027389649321255142948864 * μ ^ 2 +
    2490768607554365103399071888296743884095 / 576947634261777829871793251553551353856 * μ ^ 3 -
    79136101609023626168366717686515065415125 / 36924648592753781111794768099427286646784 * μ ^ 4 +
    1704192356206143932164770148003275383375 / 4615581074094222638974346012428410830848 * μ ^ 5 -
    44451473837071756240726312169185785551875 / 73849297185507562223589536198854573293568 * μ ^ 6),
    3, 2, 0), ((1600060374221312677045762391277763373117 / 2837447381615300802648163532230580428800
    + 302550460824477378728053702474495634361 / 75665263509741354737284360859482144768 * μ +
    53316929844976961426389228871365989469 / 1210644216155861675796549773751714316288 * μ ^ 2 +
    2777465935906272753279129042525529918915 / 576947634261777829871793251553551353856 * μ ^ 3 -
    122611253868334768112284765822627003463825 / 36924648592753781111794768099427286646784 * μ ^ 4 +
    1455471044974938615306334099816643653875 / 4615581074094222638974346012428410830848 * μ ^ 5 -
    65330112168871221380067886442297156884375 / 73849297185507562223589536198854573293568 * μ ^ 6),
    2, 3, 0), ((1557689640158385393265417139142020591 / 5823391239846692257872064714685644800 +
    772380088420826234778742482835875215023 / 453991581058448128423706165156892868608 * μ +
    10656334525726902673158424134252373715057 / 7263865296935170054779298642510285897728 * μ ^ 2 +
    5669757779857874835053245101976175030995 / 2307790537047111319487173006214205415424 * μ ^ 3 -
    167851689723762834329519542901184135529275 / 73849297185507562223589536198854573293568 * μ ^ 4 +
    3066850094926054978682577944429204556875 / 9231162148188445277948692024856821661696 * μ ^ 5 -
    145153064321537720634991210198679850385625 / 147698594371015124447179072397709146587136 * μ ^
    6), 1, 4, 0), ((4813413288169541649672450894908886622129 /
    56748947632306016052963270644611608576000 + 257750237885984874200682880736853180499 /
    453991581058448128423706165156892868608 * μ + 37664574606625972414110124867255795777297 /
    36319326484675850273896493212551429488640 * μ ^ 2 + 2404452405350708181201934101592735090187 /
    2307790537047111319487173006214205415424 * μ ^ 3 - 128998750362286109425625058543718462455295 /
    73849297185507562223589536198854573293568 * μ ^ 4 + 3756256669131799916465582760114108920975 /
    9231162148188445277948692024856821661696 * μ ^ 5 - 173225001122797072268189927751045277061125 /
    147698594371015124447179072397709146587136 * μ ^ 6), 0, 5, 0)]

/-- The jet of the first chart coordinate, degree 2. -/
def cF2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-260029 / 884360 + 961 / 44218 * μ - 10745 / 176872 * μ
    ^ 2), 2, 0, 0), ((-23639 / 442180 - 34 / 22109 * μ - 10745 / 88436 * μ ^ 2), 1, 1, 0), ((-2149 /
    884360 - 1029 / 44218 * μ - 10745 / 176872 * μ ^ 2), 0, 2, 0)]

/-- The jet of the second chart coordinate, degree 2. -/
def cG2 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((23716 / 22109 + 44817 / 44218 * μ + 4900 / 22109 * μ ^
    2), 2, 0, 0), ((4312 / 22109 + 26482 / 22109 * μ + 9800 / 22109 * μ ^ 2), 1, 1, 0), ((196 /
    22109 + 8147 / 44218 * μ + 4900 / 22109 * μ ^ 2), 0, 2, 0)]

/-- The jet of the first chart coordinate, degree 3. -/
def cF3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-2327559002905961 / 25682357114044800 - 907228064564969
    / 3424314281872640 * μ + 117223362227937 / 1369725712749056 * μ ^ 2 - 25325745803295 /
    684862856374528 * μ ^ 3 + 23167112425975 / 1369725712749056 * μ ^ 4), 3, 0, 0),
    ((-499092055244151 / 8560785704681600 - 870586166409197 / 3424314281872640 * μ + 196866414401971
    / 1369725712749056 * μ ^ 2 - 70335243045235 / 684862856374528 * μ ^ 3 + 53094147779925 /
    1369725712749056 * μ ^ 4), 2, 1, 0), ((-302762349325691 / 8560785704681600 + 52903633708863 /
    3424314281872640 * μ + 105987110719781 / 1369725712749056 * μ ^ 2 - 72518069553335 /
    684862856374528 * μ ^ 3 + 94795754420675 / 1369725712749056 * μ ^ 4), 1, 2, 0),
    ((-71946096157081 / 25682357114044800 + 92665389064591 / 3424314281872640 * μ + 48136112215747 /
    1369725712749056 * μ ^ 2 - 16746682658895 / 684862856374528 * μ ^ 3 + 64868719066725 /
    1369725712749056 * μ ^ 4), 0, 3, 0)]

/-- The jet of the second chart coordinate, degree 3. -/
def cG3 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-110538513798691 / 200643414953475 + 616016123106923 /
    3424314281872640 * μ - 53730911977 / 21401964261704 * μ ^ 2 - 651518617435 / 684862856374528 * μ
    ^ 3 - 2641201742375 / 42803928523408 * μ ^ 4), 3, 0, 0), ((-1854857771506 / 66881138317825 +
    950228669318439 / 3424314281872640 * μ + 13311257091 / 205788117901 * μ ^ 2 + 138074379725345 /
    684862856374528 * μ ^ 3 - 6053078737125 / 42803928523408 * μ ^ 4), 2, 1, 0), ((14334841162783 /
    133762276635650 - 1772018979855341 / 3424314281872640 * μ + 1708544998609 / 21401964261704 * μ ^
    2 + 6190658859245 / 684862856374528 * μ ^ 3 - 10807333565875 / 42803928523408 * μ ^ 4), 1, 2,
    0), ((3835380110753 / 401286829906950 - 308963193637357 / 3424314281872640 * μ - 1443623076041 /
    10700982130852 * μ ^ 2 + 65775561298965 / 684862856374528 * μ ^ 3 - 7395456571125 /
    42803928523408 * μ ^ 4), 0, 3, 0)]

/-- The jet of the first chart coordinate, degree 4. -/
def cF4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((6131248658318551993168885717069 /
    79464856331773291493038599168000 + 767652983064587747907991215919 /
    7946485633177329149303859916800 * μ - 647089232906693321549231666617 /
    16952502684111635518514901155840 * μ ^ 2 + 6540365522511534812608748663 /
    52976570887848860995359066112 * μ ^ 3 - 22749035847512365327848935975 /
    1695250268411163551851490115584 * μ ^ 4 + 1697268158609039727184554325 /
    105953141775697721990718132224 * μ ^ 5 + 9571776348863514073637181875 /
    3390500536822327103702980231168 * μ ^ 6), 4, 0, 0), ((21316058506277323022160196529 /
    19866214082943322873259649792000 + 48796644970306727902056607609 /
    1986621408294332287325964979200 * μ + 65211612065068366494937899083 /
    4238125671027908879628725288960 * μ ^ 2 + 2019969815384770098275076089 /
    6622071360981107624419883264 * μ ^ 3 - 28897292291893369212773757825 /
    423812567102790887962872528896 * μ ^ 4 + 1102965687064538234758642325 /
    26488285443924430497679533056 * μ ^ 5 - 17301771134306014951586088125 /
    847625134205581775925745057792 * μ ^ 6), 3, 1, 0), ((-315582169116467859498281956861 /
    13244142721962215248839766528000 + 49709019672308643765634147549 /
    1324414272196221524883976652800 * μ + 477827543635726624443009035899 /
    8476251342055817759257450577920 * μ ^ 2 + 17464032364708176317104141183 /
    52976570887848860995359066112 * μ ^ 3 - 112551809899243070106213545775 /
    847625134205581775925745057792 * μ ^ 4 + 77400392693232129598806925 /
    1655517840245276906104970816 * μ ^ 5 - 60903544890617051819618830625 /
    1695250268411163551851490115584 * μ ^ 6), 2, 2, 0), ((-310842456165224022517141142101 /
    19866214082943322873259649792000 - 1371945966140634988315151921 / 48454180690105665544535731200
    * μ + 455985035787032381351302229033 / 4238125671027908879628725288960 * μ ^ 2 +
    2709064388484706845355223941 / 26488285443924430497679533056 * μ ^ 3 -
    31887594993903677554201240775 / 423812567102790887962872528896 * μ ^ 4 +
    763418296443236972998118225 / 13244142721962215248839766528 * μ ^ 5 -
    48693132467807094491523884375 / 847625134205581775925745057792 * μ ^ 6), 1, 3, 0),
    ((-147042822284162370411120805691 / 79464856331773291493038599168000 +
    5979515422387234463386441679 / 7946485633177329149303859916800 * μ +
    545089658559579389720024084783 / 16952502684111635518514901155840 * μ ^ 2 +
    323862446431085003727477749 / 26488285443924430497679533056 * μ ^ 3 -
    78961036138805942692651504375 / 1695250268411163551851490115584 * μ ^ 4 +
    1400899666711786642684067575 / 105953141775697721990718132224 * μ ^ 5 -
    176855822759833670013389723125 / 3390500536822327103702980231168 * μ ^ 6), 0, 4, 0)]

/-- The jet of the second chart coordinate, degree 4. -/
def cG4 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-253031688633033118414144948507 /
    496655352073583071831491244800 - 26524768622736758913556517732737 /
    15892971266354658298607719833600 * μ - 238336333967685989882011229911 /
    529765708878488609953590661120 * μ ^ 2 - 13900173928277433915991449067 /
    26488285443924430497679533056 * μ ^ 3 - 1505937795007274116768077665 /
    52976570887848860995359066112 * μ ^ 4 - 19673129183974102430378988525 /
    211906283551395443981436264448 * μ ^ 5 - 1091244860619618868329971875 /
    105953141775697721990718132224 * μ ^ 6), 4, 0, 0), ((-29532309385060384642318236077 /
    124163838018395767957872811200 - 6091514447128404832056039446377 /
    3973242816588664574651929958400 * μ - 143002366343900228139290881971 /
    132441427219622152488397665280 * μ ^ 2 - 11104837322375063288838019389 /
    13244142721962215248839766528 * μ ^ 3 + 2129440626089723122635244485 /
    13244142721962215248839766528 * μ ^ 4 + 766947758585944064662672475 /
    52976570887848860995359066112 * μ ^ 5 + 1972514624432281834871378125 /
    26488285443924430497679533056 * μ ^ 6), 3, 1, 0), ((-7205701371319314220450474647 /
    82775892012263845305248540800 - 1684213630831860631635221948367 /
    2648828544392443049767953305600 * μ - 188232271922384299850243821643 /
    264882854439244304976795330560 * μ ^ 2 - 1617077899907490261822453579 /
    1292111485069484414520952832 * μ ^ 3 + 12152501220632608214362218655 /
    26488285443924430497679533056 * μ ^ 4 - 15038335310651889307847452075 /
    105953141775697721990718132224 * μ ^ 5 + 6943400883295103627643840625 /
    52976570887848860995359066112 * μ ^ 6), 2, 2, 0), ((3795045568119380942442666283 /
    124163838018395767957872811200 - 574421094931229729493692670707 /
    3973242816588664574651929958400 * μ - 62325161823053534829950026641 /
    132441427219622152488397665280 * μ ^ 2 - 6041041926606153981361834173 /
    26488285443924430497679533056 * μ ^ 3 + 2471572609303470263869740035 /
    13244142721962215248839766528 * μ ^ 4 + 6214882474665694793524416975 /
    52976570887848860995359066112 * μ ^ 5 + 5551334320434033573952234375 /
    26488285443924430497679533056 * μ ^ 6), 1, 3, 0), ((2790031257509034001518684713 /
    496655352073583071831491244800 - 426820274158865352940867487897 /
    15892971266354658298607719833600 * μ - 37809574572458990239459698751 /
    529765708878488609953590661120 * μ ^ 2 - 5876968725020151507608384779 /
    52976570887848860995359066112 * μ ^ 3 + 10999315031408521170840015935 /
    52976570887848860995359066112 * μ ^ 4 - 15297312695519280109030687025 /
    211906283551395443981436264448 * μ ^ 5 + 20162715949818170848432053125 /
    105953141775697721990718132224 * μ ^ 6), 0, 4, 0)]

/-- The jet of the first chart coordinate, degree 5. -/
def cF5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((2581947110182269280677587515591858074444590383 /
    62733124160132685445748247534085902700339200000 + 1268955595109489524194110763010384666140888451
    / 5018649932810614835659859802726872216027136000 * μ +
    303395226470544767286183064172633944954665307 / 8029839892496983737055775684362995545643417600 *
    μ ^ 2 - 6737075716502691138080634873503521096429809431 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 +
    159898136676702922094229214374945208157554573 / 26123745783590187091221456893127612175159918592
    * μ ^ 4 - 3515879910206333737416809226029068269356795 /
    159291132826769433483057663982485440092438528 * μ ^ 5 +
    338827816363712145251778376573269338344381425 / 13061872891795093545610728446563806087579959296
    * μ ^ 6 + 95306439137734605469852663121620927681001375 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 +
    238029556739129936709124807673036987508138125 / 26123745783590187091221456893127612175159918592
    * μ ^ 8), 5, 0, 0), ((313766331009212972917926682536788898529697453 /
    12546624832026537089149649506817180540067840000 + 51029214867887700328646302546850683692140581 /
    200745997312424593426394392109074888641085440 * μ + 92227815890738187448324625957216131567199113
    / 1605967978499396747411155136872599109128683520 * μ ^ 2 -
    144879775723172490867024780141996802115034637 / 955746796960616600898345983894912640554631168 *
    μ ^ 3 + 5201538561550784429991789612013274647884344155 /
    78371237350770561273664370679382836525479755776 * μ ^ 4 -
    735438580891437489545808515723049544665474925 / 6530936445897546772805364223281903043789979648 *
    μ ^ 5 + 747158178189828803982189151733960276608554625 /
    13061872891795093545610728446563806087579959296 * μ ^ 6 +
    35809059600211282582458518857263554466550625 / 13061872891795093545610728446563806087579959296 *
    μ ^ 7 + 56035793804599389174483255259328255381965625 /
    26123745783590187091221456893127612175159918592 * μ ^ 8), 4, 1, 0),
    ((87869560913866719848103991635258357725377073 / 6273312416013268544574824753408590270033920000
    + 27141586142667091133425294386334923241409263 / 167288331093687161188661993424229073867571200 *
    μ - 45929341358886936715510204326422995186123991 / 802983989249698373705577568436299554564341760
    * μ ^ 2 - 1567668507104769644355074325806076040716834353 /
    19592809337692640318416092669845709131369938944 * μ ^ 3 -
    3946342179723554376046902096019477696698736135 / 39185618675385280636832185339691418262739877888
    * μ ^ 4 - 768001824610214162608695336642445070337378125 /
    3265468222948773386402682111640951521894989824 * μ ^ 5 +
    628341294762915815442401287129743927783395875 / 6530936445897546772805364223281903043789979648 *
    μ ^ 6 - 10668229203698653332837100664312723760664375 /
    502379726607503597908104940252454080291536896 * μ ^ 7 +
    477631086379336020806604224257901265754896875 / 13061872891795093545610728446563806087579959296
    * μ ^ 8), 3, 2, 0), ((-28039032237549650239751767753569250316546257 /
    6273312416013268544574824753408590270033920000 + 35761326011537817672985845131101074467610203 /
    501864993281061483565985980272687221602713600 * μ - 18794866154746789101851659590433512501722741
    / 160596797849939674741115513687259910912868352 * μ ^ 2 -
    3607406737484573157206298383710915762247072239 / 19592809337692640318416092669845709131369938944
    * μ ^ 3 - 1811886812713855491096724183353551870423324425 /
    13061872891795093545610728446563806087579959296 * μ ^ 4 -
    908255431457947757224432580345335189070155075 / 3265468222948773386402682111640951521894989824 *
    μ ^ 5 + 1208011603483116943622223335257158470588655875 /
    6530936445897546772805364223281903043789979648 * μ ^ 6 +
    57514568135419880462636349176222125368756875 / 6530936445897546772805364223281903043789979648 *
    μ ^ 7 + 701972055254521273728829439822482950722609375 /
    13061872891795093545610728446563806087579959296 * μ ^ 8), 2, 3, 0),
    ((-61785382064230632731288205613001630733980537 /
    12546624832026537089149649506817180540067840000 + 93638921491377776799234020882620830136963 /
    5939230689716703947526461305002215640268800 * μ - 56667217904338266135852751073569150178760229 /
    1605967978499396747411155136872599109128683520 * μ ^ 2 -
    2286299706393377988538438772752082902372357375 / 39185618675385280636832185339691418262739877888
    * μ ^ 3 - 16082749054945044606041709040195886907950500765 /
    78371237350770561273664370679382836525479755776 * μ ^ 4 -
    597725314471219423988512724215999369410645775 / 6530936445897546772805364223281903043789979648 *
    μ ^ 5 + 1286817013560229956969992168763554659903872125 /
    13061872891795093545610728446563806087579959296 * μ ^ 6 -
    155195639122233116134639145196022748161018125 / 13061872891795093545610728446563806087579959296
    * μ ^ 7 + 1559669676134922808222980553584814992393540625 /
    26123745783590187091221456893127612175159918592 * μ ^ 8), 1, 4, 0),
    ((-53948840237367583074856133795992502815991267 /
    62733124160132685445748247534085902700339200000 - 3415049059685640430912573557837068415680493 /
    1672883310936871611886619934242290738675712000 * μ -
    145733504901993290990436998441943175499159263 / 8029839892496983737055775684362995545643417600 *
    μ ^ 2 - 11842772806502094098378653055312807549806891861 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 -
    7593262234906083709528291851520685709146206921 / 78371237350770561273664370679382836525479755776
    * μ ^ 4 - 68443137191791844749267821957487781652620545 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 +
    1189463855767091188394624473022588289607928925 / 13061872891795093545610728446563806087579959296
    * μ ^ 6 + 9712119041948505689916547738643080322924625 /
    1004759453215007195816209880504908160583073792 * μ ^ 7 +
    1861302637064454541521700773684981502021788125 / 26123745783590187091221456893127612175159918592
    * μ ^ 8), 0, 5, 0)]

/-- The jet of the second chart coordinate, degree 5. -/
def cG5 (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((-113106665227863609514467824647525591579767107 /
    1306940086669430946786421823626789639590400000 - 1153675937642792683315561893097478452499455689
    / 1672883310936871611886619934242290738675712000 * μ -
    52442242506818827988541074082780923964122239 / 334576662187374322377323986848458147735142400 * μ
    ^ 2 + 32928515586419210300672440119836695280593719949 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 +
    23972946132472711574342910465367026629615079 / 816367055737193346600670527910237880473747456 * μ
    ^ 4 - 1097585756437939717782763695042761560254578295 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 -
    123214622218179225311632681940099393665622375 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 - 1376108285652035379812675979458721896047463125 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 -
    27136920149412207768141264718424412256628125 / 816367055737193346600670527910237880473747456 * μ
    ^ 8), 5, 0, 0), ((-43371289882979452897121770360081489235053537 /
    261388017333886189357284364725357927918080000 - 1269369666341630402881136651294788770599114561 /
    1003729986562122967131971960545374443205427200 * μ -
    79118300290839533531210673388470037250957599 / 200745997312424593426394392109074888641085440 * μ
    ^ 2 + 13092160054850959401079695223663374087476570685 /
    13061872891795093545610728446563806087579959296 * μ ^ 3 -
    249086088234876849455671385501654422728052535 / 2449101167211580039802011583730713641421242368 *
    μ ^ 4 + 3563998096990711139584883449861679144032122375 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 -
    179048652195842081303972239734973866640651125 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 + 970287985523246723597706838551678320003583125 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 -
    6388445547755630687644670795037423252015625 / 816367055737193346600670527910237880473747456 * μ
    ^ 8), 4, 1, 0), ((-64624651472282761416700777485692542675704751 /
    392082026000829284035926547088036891877120000 - 88992653103520123804868147363798310170596973 /
    100372998656212296713197196054537444320542720 * μ + 61928656897571362189711818606348386216852899
    / 100372998656212296713197196054537444320542720 * μ ^ 2 +
    27396213964522368901881794175140540729791959611 /
    19592809337692640318416092669845709131369938944 * μ ^ 3 +
    1271433398794382973219164164810819728591006095 / 1224550583605790019901005791865356820710621184
    * μ ^ 4 + 581335931450131379866187381669951495372391975 /
    3265468222948773386402682111640951521894989824 * μ ^ 5 -
    161209366276923277545088513599570948701297875 / 408183527868596673300335263955118940236873728 *
    μ ^ 6 - 42238091864106588142719450976845491173049375 /
    159291132826769433483057663982485440092438528 * μ ^ 7 -
    54453055450412901394889732407252587301046875 / 408183527868596673300335263955118940236873728 * μ
    ^ 8), 3, 2, 0), ((-9053534817767196589825146929171609951156747 /
    130694008666943094678642182362678963959040000 - 93296282332127174643155670464281689808129693 /
    167288331093687161188661993424229073867571200 * μ + 22798607795768059950068635730436238232232959
    / 33457666218737432237732398684845814773514240 * μ ^ 2 +
    27890362993253970133389086082715796640569361317 /
    19592809337692640318416092669845709131369938944 * μ ^ 3 +
    247428259095462303789982508744950560515467025 / 408183527868596673300335263955118940236873728 *
    μ ^ 4 + 3643103494716148412490035603120153393498504825 /
    3265468222948773386402682111640951521894989824 * μ ^ 5 -
    359596978887342597791884971450465695193489625 / 408183527868596673300335263955118940236873728 *
    μ ^ 6 + 279719985903167576476514081590342956034924375 /
    6530936445897546772805364223281903043789979648 * μ ^ 7 -
    80029387406867246190583160891814017183359375 / 408183527868596673300335263955118940236873728 * μ
    ^ 8), 2, 3, 0), ((-157205805027003893446846058589345349522027 /
    261388017333886189357284364725357927918080000 - 170044140346347580291285890773134019871521803 /
    1003729986562122967131971960545374443205427200 * μ +
    12971459375275210928323122289677923966057387 / 40149199462484918685278878421814977728217088 * μ
    ^ 2 + 12574282616954206048433776091320291460912236791 /
    13061872891795093545610728446563806087579959296 * μ ^ 3 +
    2064962152624847790044738721489160356957933905 / 2449101167211580039802011583730713641421242368
    * μ ^ 4 - 28725696944532482341272698001912566791733775 /
    502379726607503597908104940252454080291536896 * μ ^ 5 -
    345703255774147241654807705680473567034476375 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 - 377687468568422453101787944789451034731063125 /
    1004759453215007195816209880504908160583073792 * μ ^ 7 -
    177812503793883707777864232493382816722390625 / 816367055737193346600670527910237880473747456 *
    μ ^ 8), 1, 4, 0), ((8142681095352215701936410112533057087801229 /
    3920820260008292840359265470880368918771200000 - 61262865928709857636450658826794321379336137 /
    5018649932810614835659859802726872216027136000 * μ +
    54707597573973485400116589889721688876921173 / 1003729986562122967131971960545374443205427200 *
    μ ^ 2 + 47718473590046246133251122048795207248221819479 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 +
    701008149306524088953770456679674524839141717 / 2449101167211580039802011583730713641421242368 *
    μ ^ 4 + 841086517582774574702107203701111914977659555 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 -
    309312683691666329378933624445461920441939125 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 + 62677058762187015860426165594652232032110625 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 -
    212200626375426413528532661495030464399878125 / 816367055737193346600670527910237880473747456 *
    μ ^ 8), 0, 5, 0)]

/-- The polynomial part of the defect, degrees five to eight. -/
def highD (μ : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [((51232486654287128774171537893849964653774003 /
    1206406233848705489341312452578575051929600000 + 950050196166485835597124469994751911968669131 /
    3136656208006634272287412376704295135016960000 * μ +
    567483604082776283697917417097650045756375617 / 3345766621873743223773239868484581477351424000 *
    μ ^ 2 + 11068572542880609553508550170844807788659649 /
    83644165546843580594330996712114536933785600 * μ ^ 3 +
    92975289588011251035293937303805698417847183 / 401491994624849186852788784218149777282170880 * μ
    ^ 4 + 32201937434176714443205715244910427827331 / 418220827734217902971654983560572684668928 * μ
    ^ 5 + 2104366050025102013768990857221028048671775 / 26766132974989945790185918947876651818811392
    * μ ^ 6 + 108788569122929696550268785546456586984325 /
    3345766621873743223773239868484581477351424 * μ ^ 7 + 17140773719094134579430357639670770038375
    / 2058933305768457368475839919067434755293184 * μ ^ 8), 5, 0, 0),
    ((247239954127556920407777897554268870524399959 / 3136656208006634272287412376704295135016960000
    + 499871967057243676367648169568886891231269849 / 627331241601326854457482475340859027003392000
    * μ + 2202764765168402845536501789626290505393293063 /
    2007459973124245934263943921090748886410854400 * μ ^ 2 +
    14053128609309261538912105162037647732899287 / 12546624832026537089149649506817180540067840 * μ
    ^ 3 + 8497373358351798884005485596879896843244693 / 26766132974989945790185918947876651818811392
    * μ ^ 4 - 536278072832557021437453482371673571817355 /
    1672883310936871611886619934242290738675712 * μ ^ 5 -
    9295542539917980745960028308474428763324825 / 26766132974989945790185918947876651818811392 * μ ^
    6 - 153423437698278367021947719238663242615125 / 836441655468435805943309967121145369337856 * μ
    ^ 7 - 1146776363324901682959124760592877074270625 / 26766132974989945790185918947876651818811392
    * μ ^ 8), 4, 1, 0), ((2715666677291290793319955650022825260473293 /
    32673502166735773669660545590669740989760000 + 36959479685976454635301624923472092910164489 /
    104555206933554475742913745890143171167232000 * μ + 27118628095734433845603384347874907084771761
    / 16728833109368716118866199342422907386757120 * μ ^ 2 +
    4662491495911991005904572976464833149744993 / 3136656208006634272287412376704295135016960 * μ ^
    3 + 972059355696430008962279863145722981082995 / 772099989663171513178439969650288033234944 * μ
    ^ 4 - 221031728012028824582901462615470297528815 / 418220827734217902971654983560572684668928 *
    μ ^ 5 - 1052867735760064711196342401973098869599975 /
    3345766621873743223773239868484581477351424 * μ ^ 6 - 16342316985845412006511061066955913831375
    / 64341665805264292764869997470857336102912 * μ ^ 7 - 399804415477763504258326200718790855201875
    / 3345766621873743223773239868484581477351424 * μ ^ 8), 3, 2, 0),
    ((-12262570434071489102701869939982811204338937 / 196041013000414642017963273544018445938560000
    + 8661464791056995635290116563715927561999291 / 31366562080066342722874123767042951350169600 * μ
    + 167685208530805163060769105195176504904715991 / 83644165546843580594330996712114536933785600 *
    μ ^ 2 + 1857126685560990530092521763144169342378457 / 836441655468435805943309967121145369337856
    * μ ^ 3 + 6578332724029794396096350690880285964837529 /
    10037299865621229671319719605453744432054272 * μ ^ 4 -
    410499018652422028792205525679992571892955 / 836441655468435805943309967121145369337856 * μ ^ 5
    - 3763005318666040734360906314741464763721275 / 3345766621873743223773239868484581477351424 * μ
    ^ 6 - 29767332689673414290094954600838440653625 / 52277603466777237871456872945071585583616 * μ
    ^ 7 - 696545739293058010236968677665779825349375 / 3345766621873743223773239868484581477351424 *
    μ ^ 8), 2, 3, 0), ((-87621571826518399596866182605999948145758571 /
    3136656208006634272287412376704295135016960000 + 41000434437335228977325733209787288761857103 /
    627331241601326854457482475340859027003392000 * μ + 36428475741905950902144129502186125057726049
    / 48962438368884047177169363929042655766118400 * μ ^ 2 +
    62475624530255874767504865995491821802933321 / 50186499328106148356598598027268722160271360 * μ
    ^ 3 + 26623915943130807666713845006139511455754719 /
    26766132974989945790185918947876651818811392 * μ ^ 4 -
    337479360393283767958007461480576285403645 / 418220827734217902971654983560572684668928 * μ ^ 5
    - 13031080558695262831554298588224617916874175 / 26766132974989945790185918947876651818811392 *
    μ ^ 6 - 2298539667005424823963409994621752851295625 /
    3345766621873743223773239868484581477351424 * μ ^ 7 -
    8995524186689975424444243130557817892196875 / 26766132974989945790185918947876651818811392 * μ ^
    8), 1, 4, 0), ((-10273815789768001050402738504536648875578337 /
    5227760346677723787145687294507158558361600000 + 5201712265453393289129788807029910042228657 /
    1045552069335544757429137458901431711672320000 * μ +
    310740933983843609509389145040005973399863087 / 3345766621873743223773239868484581477351424000 *
    μ ^ 2 + 6628760600627376796764871285436084220590269 /
    31366562080066342722874123767042951350169600 * μ ^ 3 +
    94007612239723018008016357957971318036953813 / 401491994624849186852788784218149777282170880 * μ
    ^ 4 - 31540506296428406660031507925255320592251 / 1672883310936871611886619934242290738675712 *
    μ ^ 5 - 7231466481358914128578258609666799136157175 /
    26766132974989945790185918947876651818811392 * μ ^ 6 - 38948711930392880640264312807608157187575
    / 836441655468435805943309967121145369337856 * μ ^ 7 -
    5251987174494493944123383905073309046247375 / 26766132974989945790185918947876651818811392 * μ ^
    8), 0, 5, 0), ((104321081675695748746230450466614443275203086219321683 /
    2694982875257230437235108661500593686767188627456000000 -
    943739412775676967514419765606124119133079111598542761 /
    9109042118369438877854667275872006661273097560801280000 * μ -
    32167010848950400536140201274180093781101229525430628037 /
    291489347787822044091349352827904213160739121945640960000 * μ ^ 2 +
    30503559565859731531941768987642892120249396202630691 /
    6477541061951600979807763396175649181349758265458688000 * μ ^ 3 -
    290767535491170714683581962104820864654846839521599839 /
    15546098548683842351538632150821558035239419837100851200 * μ ^ 4 +
    29708957660918870431046037097973386412270446794673363 /
    259101642478064039192310535847025967253990330618347520 * μ ^ 5 -
    14691542718527438188787153550076710465207719886946799 /
    621843941947353694061545286032862321409576793484034048 * μ ^ 6 +
    1914432317852442713862944501511012671789466263506205 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 7 -
    2839368383058665911405891136907897713743829950726975 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 8 +
    131869503233807146195485707753762796210072075938125 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 9 -
    55732886350578513697288282497380422650252751284375 /
    15944716460188556257988340667509290292553251114975232 * μ ^ 10), 6, 0, 0),
    ((1017255293559928599700195134755413169099594554016434107 /
    12651447386624220663687037883155564807323746612224000000 -
    2123108473828462009333951742776399918006297520487831329 /
    6072694745579625918569778183914671107515398373867520000 * μ -
    1968305773637845363767456413877192622635037023321151679 /
    6072694745579625918569778183914671107515398373867520000 * μ ^ 2 -
    1485453107720913242367314793893846732970553335543265939 /
    6477541061951600979807763396175649181349758265458688000 * μ ^ 3 +
    866151239994468139566779744108167571118860740960210781 /
    2591016424780640391923105358470259672539903306183475200 * μ ^ 4 +
    6081177813593125525581783955047576526757238353008979 /
    777304927434192117576931607541077901761970991855042560 * μ ^ 5 +
    20857182375250618570132476167041648262557601344791503 /
    310921970973676847030772643016431160704788396742017024 * μ ^ 6 -
    2207288688832834772530528365303622916047451425789645 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 7 +
    1977425681155866079064509360725741034489843768902575 /
    103640656991225615676924214338810386901596132247339008 * μ ^ 8 +
    42480571311070430998967393830572512206164524676875 /
    3986179115047139064497085166877322573138312778743808 * μ ^ 9 +
    849483734564218970452590341820436386585668378734375 /
    103640656991225615676924214338810386901596132247339008 * μ ^ 10), 5, 1, 0),
    ((1581617063526212854289875218302941550577375747638983937 /
    30363473727898129592848890919573355537576991869337600000 -
    6561876469580524432860754877394674110700355541029207 /
    31142024336305773941383477866229082602643068583936000 * μ -
    717049060071867149829568721067805848743485980910791979 /
    1494817168142677149186406937578995964926867292028928000 * μ ^ 2 -
    6109551705271148293721163116833867751760337477941383 /
    121453894911592518371395563678293422150307967477350400 * μ ^ 3 +
    725432520077510777128262697571818945574093648598719303 /
    3109219709736768470307726430164311607047883967420170240 * μ ^ 4 +
    2712253100124823876775457354126566908108823812328149 /
    19432623185854802939423290188526947544049274796376064 * μ ^ 5 -
    31406999077111449191440338604608018202630555381739895 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 6 -
    1243848165650449683495103798327182248839170396763975 /
    6477541061951600979807763396175649181349758265458688 * μ ^ 7 +
    4534199608234101946626467252661546731655165619387875 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 8 -
    107041568451616243163231326603623409225075614278125 /
    3238770530975800489903881698087824590674879132729344 * μ ^ 9 +
    3372567209280690411610915984695486697377949881859375 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 10), 4, 2, 0),
    ((858918728375525898760763386528491879725667569950443137 /
    22772605295923597194636668189680016653182743902003200000 -
    4706290580533323125810108559615078619365613508010709 /
    36436168473477755511418669103488026645092390243205120 * μ -
    12470568755243100128793867598825630612008057598743623597 /
    14574467389391102204567467641395210658036956097282048000 * μ ^ 2 -
    98327564865707581448344964494335617283109391759186399 /
    1943262318585480293942329018852694754404927479637606400 * μ ^ 3 +
    69580576455116940970051383867629916313059781513246073 /
    388652463717096058788465803770538950880985495927521280 * μ ^ 4 +
    8295340969165513092446053631054278468589602531099611 /
    25910164247806403919231053584702596725399033061834752 * μ ^ 5 -
    301108843998192081386400147678477959144111093899965 /
    3238770530975800489903881698087824590674879132729344 * μ ^ 6 -
    2262132069873907362723070476289924088112904230494575 /
    25910164247806403919231053584702596725399033061834752 * μ ^ 7 +
    2072262524970006797745933966608251306213814827977875 /
    25910164247806403919231053584702596725399033061834752 * μ ^ 8 +
    1110531300433715021504856869309904559708465774640625 /
    25910164247806403919231053584702596725399033061834752 * μ ^ 9 +
    4926697290190350779357496873340580519930277703125 /
    62284048672611547882766955732458165205286137167872 * μ ^ 10), 3, 3, 0),
    ((-4956865760217625496233343477418670913937913513056811 /
    10121157909299376530949630306524451845858997289779200000 +
    18468728873759006920585464813284415530282846910647651 /
    607269474557962591856977818391467110751539837386752000 * μ -
    3033970938498525981959725083313027244173758723349582217 /
    19432623185854802939423290188526947544049274796376064000 * μ ^ 2 -
    107563028957336469224760139092402478090042970483425237 /
    1295508212390320195961552679235129836269951653091737600 * μ ^ 3 +
    81459184605962141281995623458165584349953781120336441 /
    1036406569912256156769242143388103869015961322473390080 * μ ^ 4 -
    14874603377265610193152669594054449456530045887770463 /
    155460985486838423515386321508215580352394198371008512 * μ ^ 5 -
    103487731839848688303438206347080732743238780303407185 /
    621843941947353694061545286032862321409576793484034048 * μ ^ 6 -
    25997292908441257084411274247375521398650443343511175 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 7 +
    35120539267146272525766691973096930523715539661410375 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 8 -
    4632729743160427710428492156572903085625167102534375 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 9 +
    21709223977809309789511376043574495649941797892296875 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 10), 2, 4, 0),
    ((-111968009953579690398469528472465452669269290858250737 /
    18977171079936330995530556824733347210985619918336000000 +
    136239814685047567005599191825610013683554819984583887 /
    2024231581859875306189926061304890369171799457955840000 * μ -
    2427323413565421468570681963429459803486777444369309131 /
    24290778982318503674279112735658684430061593495470080000 * μ ^ 2 -
    9031386240783140495171363110599161299929974593576096237 /
    19432623185854802939423290188526947544049274796376064000 * μ ^ 3 -
    1588551693245769708124885669876034933131836584100323467 /
    7773049274341921175769316075410779017619709918550425600 * μ ^ 4 +
    230661350171994349168857313238523148084819148858622359 /
    777304927434192117576931607541077901761970991855042560 * μ ^ 5 -
    42212919488646290876372130810463241809549223301372349 /
    103640656991225615676924214338810386901596132247339008 * μ ^ 6 +
    11296780167810438294321488096041781486999707556045855 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 7 +
    10283312393429452313936674207349337434347089968070325 /
    103640656991225615676924214338810386901596132247339008 * μ ^ 8 +
    1171116868268971996482808068466698783393442048981875 /
    51820328495612807838462107169405193450798066123669504 * μ ^ 9 +
    14050901744055597783320887670617870092947223785440625 /
    103640656991225615676924214338810386901596132247339008 * μ ^ 10), 1, 5, 0),
    ((-230946972004080899010674521160532435457645001785344083 /
    455452105918471943892733363793600333063654878040064000000 +
    140391305878540009984355717717034756866266940978748583 /
    18218084236738877755709334551744013322546195121602560000 * μ -
    3577223282622111959133003850505864600631855016723914907 /
    291489347787822044091349352827904213160739121945640960000 * μ ^ 2 -
    1169307378128028184829361168517569807482133568539762641 /
    9716311592927401469711645094263473772024637398188032000 * μ ^ 3 -
    571323006780945861596464091378792364772704766827860873 /
    5182032849561280783846210716940519345079806612366950400 * μ ^ 4 +
    6459450182727225449558095960701437920672167638158489 /
    129550821239032019596155267923512983626995165309173760 * μ ^ 5 -
    18540808377526582279294722988296279192618856204870699 /
    621843941947353694061545286032862321409576793484034048 * μ ^ 6 -
    1769654983275253797096973895308172539418010157995585 /
    25910164247806403919231053584702596725399033061834752 * μ ^ 7 +
    42493196687098143377126997996778713527327435242697525 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 8 -
    1599652593824248624498816241107257313648830011383125 /
    25910164247806403919231053584702596725399033061834752 * μ ^ 9 +
    21839555874460641378191161263550028076527286516890625 /
    207281313982451231353848428677620773803192264494678016 * μ ^ 10), 0, 6, 0)]

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
  -(122 / 85) * ((16 * μ + 35 * μ ^ 2) / 80 * (x2v μ y * x2v μ y) -
    7 / 8 * (Real.cos (tv μ y) - 1) + 1 / 2 * (Real.sin (tv μ y) - tv μ y) +
    7 * μ / 8 * ((Real.cos (tv μ y) - 1) * x2v μ y) - μ / 2 * (Real.sin (tv μ y) * x2v μ y))

/-- The reactive-power nonlinearity on the manifold. -/
def F2v (μ : ℝ) (y : State 2) : ℝ :=
  (16 * μ + 35 * μ ^ 2) / 160 * (x2v μ y * x2v μ y) - 7 / 16 * (Real.cos (tv μ y) - 1) -
    (Real.sin (tv μ y) - tv μ y) + 7 * μ / 16 * ((Real.cos (tv μ y) - 1) * x2v μ y) +
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
  -(122 / 85) * ((16 * μ + 35 * μ ^ 2) / 80 * pv (lowQL μ) y - 7 / 8 * pv (low2L μ) y +
    1 / 2 * pv (low3L μ) y + 7 * μ / 8 * pv (lowCL μ) y - μ / 2 * pv (lowSL μ) y)

/-- The truncated reactive-power nonlinearity. -/
def F2low (μ : ℝ) (y : State 2) : ℝ :=
  (16 * μ + 35 * μ ^ 2) / 160 * pv (lowQL μ) y - 7 / 16 * pv (low2L μ) y - pv (low3L μ) y +
    7 * μ / 16 * pv (lowCL μ) y + μ * pv (lowSL μ) y

/-- `F₁ − F₁ˡᵒʷ = O(‖y‖⁶)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem F1_sub_low (μ : ℝ) :
    (fun y => F1v μ y - F1low μ y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have h := (((((fQ_sub_low μ).const_mul_left ((16 * μ + 35 * μ ^ 2) / 80)).sub
    ((f2_sub_low μ).const_mul_left (7 / 8))).add ((f3_sub_low μ).const_mul_left (1 / 2))).add
    ((fC_sub_low μ).const_mul_left (7 * μ / 8))).sub ((fS_sub_low μ).const_mul_left (μ / 2))
  refine (h.const_mul_left (-(122 / 85))).congr_left fun y => ?_
  simp only [F1v, F1low]
  ring

/-- `F₂ − F₂ˡᵒʷ = O(‖y‖⁶)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem F2_sub_low (μ : ℝ) :
    (fun y => F2v μ y - F2low μ y) =O[𝓝 0] fun y => ‖y‖ ^ 6 := by
  have h := ((((fQ_sub_low μ).const_mul_left ((16 * μ + 35 * μ ^ 2) / 160)).sub
    ((f2_sub_low μ).const_mul_left (7 / 16))).sub (f3_sub_low μ)).add
    (((fC_sub_low μ).const_mul_left (7 * μ / 16)).add ((fS_sub_low μ).const_mul_left μ))
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
  -(122 / 85) * ((16 * μ + 35 * μ ^ 2) / 80 * pv (lowQL4 μ) y - 7 / 8 * pv (low2L4 μ) y +
    1 / 2 * pv (low3L4 μ) y + 7 * μ / 8 * pv (lowCL4 μ) y - μ / 2 * pv (lowSL4 μ) y)

/-- `F₁ − F₁ˡᵒʷ⁴ = O(‖y‖⁵)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem F1_sub_low4 (μ : ℝ) :
    (fun y => F1v μ y - F1low4 μ y) =O[𝓝 0] fun y => ‖y‖ ^ 5 := by
  have h5 : (fun y : State 2 => -(122 / 85) * ((16 * μ + 35 * μ ^ 2) / 80 * pv (lowQL5 μ) y -
      7 / 8 * pv (low2L5 μ) y + 1 / 2 * pv (low3L5 μ) y + 7 * μ / 8 * pv (lowCL5 μ) y -
        μ / 2 * pv (lowSL5 μ) y)) =O[𝓝 0] fun y => ‖y‖ ^ 5 :=
    (((((((pv_isBigO (lowQL5 μ) (by simp [lowQL5])).const_mul_left
      ((16 * μ + 35 * μ ^ 2) / 80)).sub ((pv_isBigO (low2L5 μ) (by simp [low2L5])).const_mul_left
      (7 / 8))).add ((pv_isBigO (low3L5 μ) (by simp [low3L5])).const_mul_left (1 / 2))).add
      ((pv_isBigO (lowCL5 μ) (by simp [lowCL5])).const_mul_left (7 * μ / 8))).sub
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
  a20 := (-260029 / 884360 + 961 / 44218 * μ - 10745 / 176872 * μ ^ 2)
  a11 := (-23639 / 442180 - 34 / 22109 * μ - 10745 / 88436 * μ ^ 2)
  a02 := (-2149 / 884360 - 1029 / 44218 * μ - 10745 / 176872 * μ ^ 2)
  b20 := (23716 / 22109 + 44817 / 44218 * μ + 4900 / 22109 * μ ^ 2)
  b11 := (4312 / 22109 + 26482 / 22109 * μ + 9800 / 22109 * μ ^ 2)
  b02 := (196 / 22109 + 8147 / 44218 * μ + 4900 / 22109 * μ ^ 2)
  a30 := (-2327559002905961 / 25682357114044800 - 907228064564969 / 3424314281872640 * μ +
    117223362227937 / 1369725712749056 * μ ^ 2 - 25325745803295 / 684862856374528 * μ ^ 3 +
    23167112425975 / 1369725712749056 * μ ^ 4)
  a21 := (-499092055244151 / 8560785704681600 - 870586166409197 / 3424314281872640 * μ +
    196866414401971 / 1369725712749056 * μ ^ 2 - 70335243045235 / 684862856374528 * μ ^ 3 +
    53094147779925 / 1369725712749056 * μ ^ 4)
  a12 := (-302762349325691 / 8560785704681600 + 52903633708863 / 3424314281872640 * μ +
    105987110719781 / 1369725712749056 * μ ^ 2 - 72518069553335 / 684862856374528 * μ ^ 3 +
    94795754420675 / 1369725712749056 * μ ^ 4)
  a03 := (-71946096157081 / 25682357114044800 + 92665389064591 / 3424314281872640 * μ +
    48136112215747 / 1369725712749056 * μ ^ 2 - 16746682658895 / 684862856374528 * μ ^ 3 +
    64868719066725 / 1369725712749056 * μ ^ 4)
  b30 := (-110538513798691 / 200643414953475 + 616016123106923 / 3424314281872640 * μ - 53730911977
    / 21401964261704 * μ ^ 2 - 651518617435 / 684862856374528 * μ ^ 3 - 2641201742375 /
    42803928523408 * μ ^ 4)
  b21 := (-1854857771506 / 66881138317825 + 950228669318439 / 3424314281872640 * μ + 13311257091 /
    205788117901 * μ ^ 2 + 138074379725345 / 684862856374528 * μ ^ 3 - 6053078737125 /
    42803928523408 * μ ^ 4)
  b12 := (14334841162783 / 133762276635650 - 1772018979855341 / 3424314281872640 * μ + 1708544998609
    / 21401964261704 * μ ^ 2 + 6190658859245 / 684862856374528 * μ ^ 3 - 10807333565875 /
    42803928523408 * μ ^ 4)
  b03 := (3835380110753 / 401286829906950 - 308963193637357 / 3424314281872640 * μ - 1443623076041 /
    10700982130852 * μ ^ 2 + 65775561298965 / 684862856374528 * μ ^ 3 - 7395456571125 /
    42803928523408 * μ ^ 4)
  a40 := (6131248658318551993168885717069 / 79464856331773291493038599168000 +
    767652983064587747907991215919 / 7946485633177329149303859916800 * μ -
    647089232906693321549231666617 / 16952502684111635518514901155840 * μ ^ 2 +
    6540365522511534812608748663 / 52976570887848860995359066112 * μ ^ 3 -
    22749035847512365327848935975 / 1695250268411163551851490115584 * μ ^ 4 +
    1697268158609039727184554325 / 105953141775697721990718132224 * μ ^ 5 +
    9571776348863514073637181875 / 3390500536822327103702980231168 * μ ^ 6)
  a31 := (21316058506277323022160196529 / 19866214082943322873259649792000 +
    48796644970306727902056607609 / 1986621408294332287325964979200 * μ +
    65211612065068366494937899083 / 4238125671027908879628725288960 * μ ^ 2 +
    2019969815384770098275076089 / 6622071360981107624419883264 * μ ^ 3 -
    28897292291893369212773757825 / 423812567102790887962872528896 * μ ^ 4 +
    1102965687064538234758642325 / 26488285443924430497679533056 * μ ^ 5 -
    17301771134306014951586088125 / 847625134205581775925745057792 * μ ^ 6)
  a22 := (-315582169116467859498281956861 / 13244142721962215248839766528000 +
    49709019672308643765634147549 / 1324414272196221524883976652800 * μ +
    477827543635726624443009035899 / 8476251342055817759257450577920 * μ ^ 2 +
    17464032364708176317104141183 / 52976570887848860995359066112 * μ ^ 3 -
    112551809899243070106213545775 / 847625134205581775925745057792 * μ ^ 4 +
    77400392693232129598806925 / 1655517840245276906104970816 * μ ^ 5 -
    60903544890617051819618830625 / 1695250268411163551851490115584 * μ ^ 6)
  a13 := (-310842456165224022517141142101 / 19866214082943322873259649792000 -
    1371945966140634988315151921 / 48454180690105665544535731200 * μ +
    455985035787032381351302229033 / 4238125671027908879628725288960 * μ ^ 2 +
    2709064388484706845355223941 / 26488285443924430497679533056 * μ ^ 3 -
    31887594993903677554201240775 / 423812567102790887962872528896 * μ ^ 4 +
    763418296443236972998118225 / 13244142721962215248839766528 * μ ^ 5 -
    48693132467807094491523884375 / 847625134205581775925745057792 * μ ^ 6)
  a04 := (-147042822284162370411120805691 / 79464856331773291493038599168000 +
    5979515422387234463386441679 / 7946485633177329149303859916800 * μ +
    545089658559579389720024084783 / 16952502684111635518514901155840 * μ ^ 2 +
    323862446431085003727477749 / 26488285443924430497679533056 * μ ^ 3 -
    78961036138805942692651504375 / 1695250268411163551851490115584 * μ ^ 4 +
    1400899666711786642684067575 / 105953141775697721990718132224 * μ ^ 5 -
    176855822759833670013389723125 / 3390500536822327103702980231168 * μ ^ 6)
  b40 := (-253031688633033118414144948507 / 496655352073583071831491244800 -
    26524768622736758913556517732737 / 15892971266354658298607719833600 * μ -
    238336333967685989882011229911 / 529765708878488609953590661120 * μ ^ 2 -
    13900173928277433915991449067 / 26488285443924430497679533056 * μ ^ 3 -
    1505937795007274116768077665 / 52976570887848860995359066112 * μ ^ 4 -
    19673129183974102430378988525 / 211906283551395443981436264448 * μ ^ 5 -
    1091244860619618868329971875 / 105953141775697721990718132224 * μ ^ 6)
  b31 := (-29532309385060384642318236077 / 124163838018395767957872811200 -
    6091514447128404832056039446377 / 3973242816588664574651929958400 * μ -
    143002366343900228139290881971 / 132441427219622152488397665280 * μ ^ 2 -
    11104837322375063288838019389 / 13244142721962215248839766528 * μ ^ 3 +
    2129440626089723122635244485 / 13244142721962215248839766528 * μ ^ 4 +
    766947758585944064662672475 / 52976570887848860995359066112 * μ ^ 5 +
    1972514624432281834871378125 / 26488285443924430497679533056 * μ ^ 6)
  b22 := (-7205701371319314220450474647 / 82775892012263845305248540800 -
    1684213630831860631635221948367 / 2648828544392443049767953305600 * μ -
    188232271922384299850243821643 / 264882854439244304976795330560 * μ ^ 2 -
    1617077899907490261822453579 / 1292111485069484414520952832 * μ ^ 3 +
    12152501220632608214362218655 / 26488285443924430497679533056 * μ ^ 4 -
    15038335310651889307847452075 / 105953141775697721990718132224 * μ ^ 5 +
    6943400883295103627643840625 / 52976570887848860995359066112 * μ ^ 6)
  b13 := (3795045568119380942442666283 / 124163838018395767957872811200 -
    574421094931229729493692670707 / 3973242816588664574651929958400 * μ -
    62325161823053534829950026641 / 132441427219622152488397665280 * μ ^ 2 -
    6041041926606153981361834173 / 26488285443924430497679533056 * μ ^ 3 +
    2471572609303470263869740035 / 13244142721962215248839766528 * μ ^ 4 +
    6214882474665694793524416975 / 52976570887848860995359066112 * μ ^ 5 +
    5551334320434033573952234375 / 26488285443924430497679533056 * μ ^ 6)
  b04 := (2790031257509034001518684713 / 496655352073583071831491244800 -
    426820274158865352940867487897 / 15892971266354658298607719833600 * μ -
    37809574572458990239459698751 / 529765708878488609953590661120 * μ ^ 2 -
    5876968725020151507608384779 / 52976570887848860995359066112 * μ ^ 3 +
    10999315031408521170840015935 / 52976570887848860995359066112 * μ ^ 4 -
    15297312695519280109030687025 / 211906283551395443981436264448 * μ ^ 5 +
    20162715949818170848432053125 / 105953141775697721990718132224 * μ ^ 6)
  a50 := (2581947110182269280677587515591858074444590383 /
    62733124160132685445748247534085902700339200000 + 1268955595109489524194110763010384666140888451
    / 5018649932810614835659859802726872216027136000 * μ +
    303395226470544767286183064172633944954665307 / 8029839892496983737055775684362995545643417600 *
    μ ^ 2 - 6737075716502691138080634873503521096429809431 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 +
    159898136676702922094229214374945208157554573 / 26123745783590187091221456893127612175159918592
    * μ ^ 4 - 3515879910206333737416809226029068269356795 /
    159291132826769433483057663982485440092438528 * μ ^ 5 +
    338827816363712145251778376573269338344381425 / 13061872891795093545610728446563806087579959296
    * μ ^ 6 + 95306439137734605469852663121620927681001375 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 +
    238029556739129936709124807673036987508138125 / 26123745783590187091221456893127612175159918592
    * μ ^ 8)
  a41 := (313766331009212972917926682536788898529697453 /
    12546624832026537089149649506817180540067840000 + 51029214867887700328646302546850683692140581 /
    200745997312424593426394392109074888641085440 * μ + 92227815890738187448324625957216131567199113
    / 1605967978499396747411155136872599109128683520 * μ ^ 2 -
    144879775723172490867024780141996802115034637 / 955746796960616600898345983894912640554631168 *
    μ ^ 3 + 5201538561550784429991789612013274647884344155 /
    78371237350770561273664370679382836525479755776 * μ ^ 4 -
    735438580891437489545808515723049544665474925 / 6530936445897546772805364223281903043789979648 *
    μ ^ 5 + 747158178189828803982189151733960276608554625 /
    13061872891795093545610728446563806087579959296 * μ ^ 6 +
    35809059600211282582458518857263554466550625 / 13061872891795093545610728446563806087579959296 *
    μ ^ 7 + 56035793804599389174483255259328255381965625 /
    26123745783590187091221456893127612175159918592 * μ ^ 8)
  a32 := (87869560913866719848103991635258357725377073 /
    6273312416013268544574824753408590270033920000 + 27141586142667091133425294386334923241409263 /
    167288331093687161188661993424229073867571200 * μ - 45929341358886936715510204326422995186123991
    / 802983989249698373705577568436299554564341760 * μ ^ 2 -
    1567668507104769644355074325806076040716834353 / 19592809337692640318416092669845709131369938944
    * μ ^ 3 - 3946342179723554376046902096019477696698736135 /
    39185618675385280636832185339691418262739877888 * μ ^ 4 -
    768001824610214162608695336642445070337378125 / 3265468222948773386402682111640951521894989824 *
    μ ^ 5 + 628341294762915815442401287129743927783395875 /
    6530936445897546772805364223281903043789979648 * μ ^ 6 -
    10668229203698653332837100664312723760664375 / 502379726607503597908104940252454080291536896 * μ
    ^ 7 + 477631086379336020806604224257901265754896875 /
    13061872891795093545610728446563806087579959296 * μ ^ 8)
  a23 := (-28039032237549650239751767753569250316546257 /
    6273312416013268544574824753408590270033920000 + 35761326011537817672985845131101074467610203 /
    501864993281061483565985980272687221602713600 * μ - 18794866154746789101851659590433512501722741
    / 160596797849939674741115513687259910912868352 * μ ^ 2 -
    3607406737484573157206298383710915762247072239 / 19592809337692640318416092669845709131369938944
    * μ ^ 3 - 1811886812713855491096724183353551870423324425 /
    13061872891795093545610728446563806087579959296 * μ ^ 4 -
    908255431457947757224432580345335189070155075 / 3265468222948773386402682111640951521894989824 *
    μ ^ 5 + 1208011603483116943622223335257158470588655875 /
    6530936445897546772805364223281903043789979648 * μ ^ 6 +
    57514568135419880462636349176222125368756875 / 6530936445897546772805364223281903043789979648 *
    μ ^ 7 + 701972055254521273728829439822482950722609375 /
    13061872891795093545610728446563806087579959296 * μ ^ 8)
  a14 := (-61785382064230632731288205613001630733980537 /
    12546624832026537089149649506817180540067840000 + 93638921491377776799234020882620830136963 /
    5939230689716703947526461305002215640268800 * μ - 56667217904338266135852751073569150178760229 /
    1605967978499396747411155136872599109128683520 * μ ^ 2 -
    2286299706393377988538438772752082902372357375 / 39185618675385280636832185339691418262739877888
    * μ ^ 3 - 16082749054945044606041709040195886907950500765 /
    78371237350770561273664370679382836525479755776 * μ ^ 4 -
    597725314471219423988512724215999369410645775 / 6530936445897546772805364223281903043789979648 *
    μ ^ 5 + 1286817013560229956969992168763554659903872125 /
    13061872891795093545610728446563806087579959296 * μ ^ 6 -
    155195639122233116134639145196022748161018125 / 13061872891795093545610728446563806087579959296
    * μ ^ 7 + 1559669676134922808222980553584814992393540625 /
    26123745783590187091221456893127612175159918592 * μ ^ 8)
  a05 := (-53948840237367583074856133795992502815991267 /
    62733124160132685445748247534085902700339200000 - 3415049059685640430912573557837068415680493 /
    1672883310936871611886619934242290738675712000 * μ -
    145733504901993290990436998441943175499159263 / 8029839892496983737055775684362995545643417600 *
    μ ^ 2 - 11842772806502094098378653055312807549806891861 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 -
    7593262234906083709528291851520685709146206921 / 78371237350770561273664370679382836525479755776
    * μ ^ 4 - 68443137191791844749267821957487781652620545 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 +
    1189463855767091188394624473022588289607928925 / 13061872891795093545610728446563806087579959296
    * μ ^ 6 + 9712119041948505689916547738643080322924625 /
    1004759453215007195816209880504908160583073792 * μ ^ 7 +
    1861302637064454541521700773684981502021788125 / 26123745783590187091221456893127612175159918592
    * μ ^ 8)
  b50 := (-113106665227863609514467824647525591579767107 /
    1306940086669430946786421823626789639590400000 - 1153675937642792683315561893097478452499455689
    / 1672883310936871611886619934242290738675712000 * μ -
    52442242506818827988541074082780923964122239 / 334576662187374322377323986848458147735142400 * μ
    ^ 2 + 32928515586419210300672440119836695280593719949 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 +
    23972946132472711574342910465367026629615079 / 816367055737193346600670527910237880473747456 * μ
    ^ 4 - 1097585756437939717782763695042761560254578295 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 -
    123214622218179225311632681940099393665622375 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 - 1376108285652035379812675979458721896047463125 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 -
    27136920149412207768141264718424412256628125 / 816367055737193346600670527910237880473747456 * μ
    ^ 8)
  b41 := (-43371289882979452897121770360081489235053537 /
    261388017333886189357284364725357927918080000 - 1269369666341630402881136651294788770599114561 /
    1003729986562122967131971960545374443205427200 * μ -
    79118300290839533531210673388470037250957599 / 200745997312424593426394392109074888641085440 * μ
    ^ 2 + 13092160054850959401079695223663374087476570685 /
    13061872891795093545610728446563806087579959296 * μ ^ 3 -
    249086088234876849455671385501654422728052535 / 2449101167211580039802011583730713641421242368 *
    μ ^ 4 + 3563998096990711139584883449861679144032122375 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 -
    179048652195842081303972239734973866640651125 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 + 970287985523246723597706838551678320003583125 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 -
    6388445547755630687644670795037423252015625 / 816367055737193346600670527910237880473747456 * μ
    ^ 8)
  b32 := (-64624651472282761416700777485692542675704751 /
    392082026000829284035926547088036891877120000 - 88992653103520123804868147363798310170596973 /
    100372998656212296713197196054537444320542720 * μ + 61928656897571362189711818606348386216852899
    / 100372998656212296713197196054537444320542720 * μ ^ 2 +
    27396213964522368901881794175140540729791959611 /
    19592809337692640318416092669845709131369938944 * μ ^ 3 +
    1271433398794382973219164164810819728591006095 / 1224550583605790019901005791865356820710621184
    * μ ^ 4 + 581335931450131379866187381669951495372391975 /
    3265468222948773386402682111640951521894989824 * μ ^ 5 -
    161209366276923277545088513599570948701297875 / 408183527868596673300335263955118940236873728 *
    μ ^ 6 - 42238091864106588142719450976845491173049375 /
    159291132826769433483057663982485440092438528 * μ ^ 7 -
    54453055450412901394889732407252587301046875 / 408183527868596673300335263955118940236873728 * μ
    ^ 8)
  b23 := (-9053534817767196589825146929171609951156747 /
    130694008666943094678642182362678963959040000 - 93296282332127174643155670464281689808129693 /
    167288331093687161188661993424229073867571200 * μ + 22798607795768059950068635730436238232232959
    / 33457666218737432237732398684845814773514240 * μ ^ 2 +
    27890362993253970133389086082715796640569361317 /
    19592809337692640318416092669845709131369938944 * μ ^ 3 +
    247428259095462303789982508744950560515467025 / 408183527868596673300335263955118940236873728 *
    μ ^ 4 + 3643103494716148412490035603120153393498504825 /
    3265468222948773386402682111640951521894989824 * μ ^ 5 -
    359596978887342597791884971450465695193489625 / 408183527868596673300335263955118940236873728 *
    μ ^ 6 + 279719985903167576476514081590342956034924375 /
    6530936445897546772805364223281903043789979648 * μ ^ 7 -
    80029387406867246190583160891814017183359375 / 408183527868596673300335263955118940236873728 * μ
    ^ 8)
  b14 := (-157205805027003893446846058589345349522027 /
    261388017333886189357284364725357927918080000 - 170044140346347580291285890773134019871521803 /
    1003729986562122967131971960545374443205427200 * μ +
    12971459375275210928323122289677923966057387 / 40149199462484918685278878421814977728217088 * μ
    ^ 2 + 12574282616954206048433776091320291460912236791 /
    13061872891795093545610728446563806087579959296 * μ ^ 3 +
    2064962152624847790044738721489160356957933905 / 2449101167211580039802011583730713641421242368
    * μ ^ 4 - 28725696944532482341272698001912566791733775 /
    502379726607503597908104940252454080291536896 * μ ^ 5 -
    345703255774147241654807705680473567034476375 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 - 377687468568422453101787944789451034731063125 /
    1004759453215007195816209880504908160583073792 * μ ^ 7 -
    177812503793883707777864232493382816722390625 / 816367055737193346600670527910237880473747456 *
    μ ^ 8)
  b05 := (8142681095352215701936410112533057087801229 /
    3920820260008292840359265470880368918771200000 - 61262865928709857636450658826794321379336137 /
    5018649932810614835659859802726872216027136000 * μ +
    54707597573973485400116589889721688876921173 / 1003729986562122967131971960545374443205427200 *
    μ ^ 2 + 47718473590046246133251122048795207248221819479 /
    195928093376926403184160926698457091313699389440 * μ ^ 3 +
    701008149306524088953770456679674524839141717 / 2449101167211580039802011583730713641421242368 *
    μ ^ 4 + 841086517582774574702107203701111914977659555 /
    6530936445897546772805364223281903043789979648 * μ ^ 5 -
    309312683691666329378933624445461920441939125 / 816367055737193346600670527910237880473747456 *
    μ ^ 6 + 62677058762187015860426165594652232032110625 /
    13061872891795093545610728446563806087579959296 * μ ^ 7 -
    212200626375426413528532661495030464399878125 / 816367055737193346600670527910237880473747456 *
    μ ^ 8)

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
@[tmio M, powerlib_domain] theorem jv_c30 (μ : ℝ) : (jet μ).c30 1 = (458521 / 663270 + 61043 / 66327
    * μ + 48055 / 132654 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c30]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `c21` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c21 (μ : ℝ) : (jet μ).c21 1 = (260029 / 442180 - 961 / 22109 *
    μ + 10745 / 88436 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c21]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `c12` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c12 (μ : ℝ) : (jet μ).c12 1 = (392 / 22109 + 8147 / 22109 * μ
    + 9800 / 22109 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c12]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `c03` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_c03 (μ : ℝ) : (jet μ).c03 1 = (349727 / 1326540 - 53857 /
    66327 * μ - 46165 / 265308 * μ ^ 2) := by
  simp only [PlanarFocus.Jet.c03]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d40` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d40 (μ : ℝ) : (jet μ).d40 1 = (-2488842714359461 /
    8560785704681600 + 39145995993433 / 214019642617040 * μ - 213201803474117 / 1369725712749056 * μ
    ^ 2 - 1318291815015 / 6585219772832 * μ ^ 3 - 156195131508675 / 1369725712749056 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d40]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d31` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d31 (μ : ℝ) : (jet μ).d31 1 = (4946058622187257 /
    25682357114044800 + 1058009571276987 / 3424314281872640 * μ - 37818166798727 / 85607857046816 *
    μ ^ 2 - 49573156471615 / 684862856374528 * μ ^ 3 - 4612558653675 / 26340879091328 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d31]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d22` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d22 (μ : ℝ) : (jet μ).d22 1 = (4616326743071579 /
    25682357114044800 - 464340246248543 / 1712157140936320 * μ - 1632717880615325 / 1369725712749056
    * μ ^ 2 - 249121099846465 / 342431428187264 * μ ^ 3 - 351868628446475 / 1369725712749056 * μ ^
    4) := by
  simp only [PlanarFocus.Jet.d22]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `d13` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_d13 (μ : ℝ) : (jet μ).d13 1 = (-160664151768623 /
    25682357114044800 + 260670220062105 / 684862856374528 * μ - 6278543587789 / 52681758182656 * μ ^
    2 - 205279464172825 / 684862856374528 * μ ^ 3 - 210797871111625 / 684862856374528 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `l1` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l1 (μ : ℝ) : (jet μ).l1 1 = (12522210601 / 387208182400 -
    67877508867 / 154883272960 * μ - 13614838531 / 30976654592 * μ ^ 2 - 5481073185 / 30976654592 *
    μ ^ 3 - 5587463875 / 30976654592 * μ ^ 4) := by
  simp only [PlanarFocus.Jet.l1]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r50 (μ : ℝ) : (jet μ).r50 1 = (7584766189077328158853180610669
    / 39732428165886645746519299584000 - 756963143593517424071785435699 /
    3973242816588664574651929958400 * μ - 16617393977895611615365709439787 /
    25428754026167453277772351733760 * μ ^ 2 - 3693777207522597844361622615 /
    26488285443924430497679533056 * μ ^ 3 - 205103398692534026264857013415 /
    847625134205581775925745057792 * μ ^ 4 - 6022207540472179386178627625 /
    52976570887848860995359066112 * μ ^ 5 + 9207263575872000810519453875 /
    1695250268411163551851490115584 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r50]
  rw [jv_c30, jv_c21, jv_d40, jv_d31]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r41 (μ : ℝ) : (jet μ).r41 1 =
    (-4791064217626674468752798661281 / 4966553520735830718314912448000 -
    37665038540660866813118474897963 / 7946485633177329149303859916800 * μ -
    4676068862911047065106082432139 / 1271437701308372663888617586688 * μ ^ 2 -
    65030743206945766247769927489 / 13244142721962215248839766528 * μ ^ 3 -
    46045986922992018530069535845 / 16300483350107341844725866496 * μ ^ 4 -
    118497330245752379863638286975 / 105953141775697721990718132224 * μ ^ 5 -
    1976658850110687681345784125 / 10336891880555875316167622656 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r41]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r32 (μ : ℝ) : (jet μ).r32 1 =
    (-22302697398054692919691517491967 / 19866214082943322873259649792000 -
    1657478619545341251166004591 / 3230278712673711036302382080 * μ -
    4651572196131311064581048187477 / 4238125671027908879628725288960 * μ ^ 2 -
    140980852663127320585166364451 / 26488285443924430497679533056 * μ ^ 3 -
    1848038867555555816733403678895 / 423812567102790887962872528896 * μ ^ 4 -
    24935937839801943466759372825 / 13244142721962215248839766528 * μ ^ 5 -
    256885834830681796470711220625 / 847625134205581775925745057792 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r32]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r23 (μ : ℝ) : (jet μ).r23 1 =
    (-2836937226994586569656311121557 / 9933107041471661436629824896000 -
    1096774250919760650323132817601 / 1324414272196221524883976652800 * μ -
    121021357938266335420909853003 / 163004833501073418447258664960 * μ ^ 2 -
    89742264941105804875791163401 / 26488285443924430497679533056 * μ ^ 3 -
    304653767411203261496963651175 / 211906283551395443981436264448 * μ ^ 4 -
    92935060555396889499400825325 / 52976570887848860995359066112 * μ ^ 5 -
    147668454684702248385372589375 / 423812567102790887962872528896 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r23]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r14 (μ : ℝ) : (jet μ).r14 1 = (5479105086834021142006584368389
    / 39732428165886645746519299584000 - 3796605732221736364608507755147 /
    3973242816588664574651929958400 * μ + 2868162318918092922517470005705 /
    5085750805233490655554470346752 * μ ^ 2 - 228023711596818719734513333 /
    827758920122638453052485408 * μ ^ 3 - 14535785793873911730327081015 /
    847625134205581775925745057792 * μ ^ 4 + 730734116024025222982192425 /
    1292111485069484414520952832 * μ ^ 5 + 338384808155519345037288240875 /
    1695250268411163551851490115584 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r14]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r05 (μ : ℝ) : (jet μ).r05 1 = (7453862341981568931069353527 /
    397324281658866457465192995840 - 1189488349030758605404704972283 /
    7946485633177329149303859916800 * μ - 3325052083495332417577173971 /
    99331070414716614366298248960 * μ ^ 2 + 6217005846596522238582754257 /
    26488285443924430497679533056 * μ ^ 3 + 1820251840532418194676567905 /
    13244142721962215248839766528 * μ ^ 4 + 27372694958193785410004241125 /
    105953141775697721990718132224 * μ ^ 5 + 13521716569579582362471633125 /
    26488285443924430497679533056 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.r05]
  rw [jv_c12, jv_c03, jv_d13]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `e50` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e50 (μ : ℝ) : (jet μ).e50 1 = (-164647436456764530828077717527
    / 744983028110374607747236867200 - 27134462685053159417294131656673 /
    23839456899531987447911579750400 * μ - 81283125529600090337221718089471 /
    95357827598127949791646319001600 * μ ^ 2 - 2166387259796308455539749407 /
    1655517840245276906104970816 * μ ^ 3 - 434421757846189143349607701693 /
    635718850654186331944308793344 * μ ^ 4 - 101650134658658882861696846645 /
    317859425327093165972154396672 * μ ^ 5 + 238462754594633492164018482775 /
    1271437701308372663888617586688 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e50]
  rw [jv_r41, jv_r23, jv_r05]
  ring

/-- The Lyapunov chain of the jet: `e41` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e41 (μ : ℝ) : (jet μ).e41 1 =
    (-7584766189077328158853180610669 / 39732428165886645746519299584000 +
    756963143593517424071785435699 / 3973242816588664574651929958400 * μ +
    16617393977895611615365709439787 / 25428754026167453277772351733760 * μ ^ 2 +
    3693777207522597844361622615 / 26488285443924430497679533056 * μ ^ 3 +
    205103398692534026264857013415 / 847625134205581775925745057792 * μ ^ 4 +
    6022207540472179386178627625 / 52976570887848860995359066112 * μ ^ 5 -
    9207263575872000810519453875 / 1695250268411163551851490115584 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e41]
  rw [jv_r50]
  ring

/-- The Lyapunov chain of the jet: `e32` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e32 (μ : ℝ) : (jet μ).e32 1 =
    (-2091550992796429676549375768857 / 29799321124414984309889474688000 -
    5669299450820799161778808397369 / 11919728449765993723955789875200 * μ -
    5571046292967192180315240803693 / 19071565519625589958329263800320 * μ ^ 2 -
    21624747184906571973820048791 / 26488285443924430497679533056 * μ ^ 3 -
    188157649617128497037663305255 / 635718850654186331944308793344 * μ ^ 4 -
    38189670639009318679392343075 / 158929712663546582986077198336 * μ ^ 5 +
    717721405768391022812811930625 / 1271437701308372663888617586688 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e32]
  rw [jv_r23, jv_r05]
  ring

/-- The Lyapunov chain of the jet: `e23` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e23 (μ : ℝ) : (jet μ).e23 1 = (7133165019900036601985156270629
    / 59598642248829968619778949376000 + 2533275638207419717610663694863 /
    5959864224882996861977894937600 * μ + 9437900908837031284894912688401 /
    7628626207850235983331705520128 * μ ^ 2 + 155755961493217711962612854911 /
    79464856331773291493038599168 * μ ^ 3 + 2258245664940623869263117705725 /
    1271437701308372663888617586688 * μ ^ 4 + 396899299747104139140230775 /
    509390104690854432647683328 * μ ^ 5 + 238471307678937794849672312875 /
    2542875402616745327777235173376 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e23]
  rw [jv_r50, jv_r32]
  ring

/-- The Lyapunov chain of the jet: `e14` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e14 (μ : ℝ) : (jet μ).e14 1 = (7453862341981568931069353527 /
    397324281658866457465192995840 - 1189488349030758605404704972283 /
    7946485633177329149303859916800 * μ - 3325052083495332417577173971 /
    99331070414716614366298248960 * μ ^ 2 + 6217005846596522238582754257 /
    26488285443924430497679533056 * μ ^ 3 + 1820251840532418194676567905 /
    13244142721962215248839766528 * μ ^ 4 + 27372694958193785410004241125 /
    105953141775697721990718132224 * μ ^ 5 + 13521716569579582362471633125 /
    26488285443924430497679533056 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e14]
  rw [jv_r05]
  ring

/-- The Lyapunov chain of the jet: `e05` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_e05 (μ : ℝ) : (jet μ).e05 1 =
    (12095344819098082981920871977349 / 595986422488299686197789493760000 +
    21522919749494887964268178044893 / 59598642248829968619778949376000 * μ +
    29147116678593846372027240736489 / 76286262078502359833317055201280 * μ ^ 2 +
    33340219929973002101973898979 / 39732428165886645746519299584 * μ ^ 3 +
    1815318003428823442448690413189 / 2542875402616745327777235173376 * μ ^ 4 +
    10518991118082525359779622355 / 52976570887848860995359066112 * μ ^ 5 -
    12253838750161371142635094225 / 5085750805233490655554470346752 * μ ^ 6) := by
  simp only [PlanarFocus.Jet5.e05]
  rw [jv_r50, jv_r32, jv_r14]
  ring

/-- The Lyapunov chain of the jet: `r60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r60 (μ : ℝ) : (jet μ).r60 1 =
    (5850058513566273748713416893412229856724073379 /
    94099686240199028168622371301128854050508800000 + 4331593659400955315424907869028833507630295189
    / 2509324966405307417829929901363436108013568000 * μ +
    26534342788028937922738157756123920738439929163 /
    12044759838745475605583663526544493318465126400 * μ ^ 2 +
    890115843753930935583207499876564014038741927947 /
    293892140065389604776241390047685636970549084160 * μ ^ 3 +
    250181919624388535697439556023620840303831787229 /
    117556856026155841910496556019074254788219633664 * μ ^ 4 +
    11739065972939205349949126055498916680270857735 / 9796404668846320159208046334922854565684969472
    * μ ^ 5 + 978475272587306434154855476859004958427850525 /
    6530936445897546772805364223281903043789979648 * μ ^ 6 +
    3411688518630509763008204495512331472958706125 / 19592809337692640318416092669845709131369938944
    * μ ^ 7 - 1373186616675884120828279078418696201866440625 /
    39185618675385280636832185339691418262739877888 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r60]
  rw [jv_c30, jv_c21, jv_d40, jv_d31, jv_e50, jv_e41]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r51 (μ : ℝ) : (jet μ).r51 1 =
    (-26367735629791446086048725286896855598566843993 /
    94099686240199028168622371301128854050508800000 - 2729402745997446056311287487488366115008081421
    / 940996862401990281686223713011288540505088000 * μ -
    12768530908657506690374136642038187371167783189 / 4014919946248491868527887842181497772821708800
    * μ ^ 2 - 16911009824434217473806205912831639692298677151 /
    14694607003269480238812069502384281848527454208 * μ ^ 3 -
    4487786616572336033242620993922653174018117695 / 2867240390881849802695037951684737921663893504
    * μ ^ 4 - 2930406591467688740380950574863210475703955425 /
    2449101167211580039802011583730713641421242368 * μ ^ 5 +
    20729998653198064723846260600062382440480913175 /
    19592809337692640318416092669845709131369938944 * μ ^ 6 +
    5089744044755493815824717583791650763021246375 / 4898202334423160079604023167461427282842484736
    * μ ^ 7 + 3186499201129496206935164342642292165113771875 /
    39185618675385280636832185339691418262739877888 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r51]
  rw [jv_c30, jv_c21, jv_c12, jv_d40, jv_d31, jv_d22, jv_e50, jv_e41, jv_e32]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r42 (μ : ℝ) : (jet μ).r42 1 =
    (-1674140018432499267443551114979887087158632657 /
    4704984312009951408431118565056442702525440000 - 14514136200022085907133235786750147114274078649
    / 7527974899215922253489789704090308324040704000 * μ +
    4295074686797001329918570372986149790404193781 / 669153324374748644754647973696916295470284800 *
    μ ^ 2 + 3914553498091089825737081842869949348334667942083 /
    293892140065389604776241390047685636970549084160 * μ ^ 3 +
    616154329200380233145132109011581622485614911291 /
    58778428013077920955248278009537127394109816832 * μ ^ 4 +
    81402523091972256411659703583029408455527801055 / 9796404668846320159208046334922854565684969472
    * μ ^ 5 + 30622002556608746350308114012988929260143180525 /
    9796404668846320159208046334922854565684969472 * μ ^ 6 +
    48423436830069619382510033357747205718314159125 /
    19592809337692640318416092669845709131369938944 * μ ^ 7 +
    12140634927173766272005566107458553052038910625 /
    19592809337692640318416092669845709131369938944 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r42]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e50, jv_e41, jv_e32,
    jv_e23]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r33 (μ : ℝ) : (jet μ).r33 1 =
    (-1496017946697908421286035378464433467546456093 /
    3136656208006634272287412376704295135016960000 - 78710232719266329771911043672558359153891593 /
    26138801733388618935728436472535792791808000 * μ +
    9728787018507608915146582630983793446454112777 / 2007459973124245934263943921090748886410854400
    * μ ^ 2 + 29853133726633176234674659837306802135091721777 /
    2449101167211580039802011583730713641421242368 * μ ^ 3 +
    261255996327456497930744064709704352341135128989 /
    19592809337692640318416092669845709131369938944 * μ ^ 4 +
    12179883879933392458608548763633575008892760605 / 1224550583605790019901005791865356820710621184
    * μ ^ 5 + 80243195002072779092912227197092233655721308125 /
    9796404668846320159208046334922854565684969472 * μ ^ 6 +
    2661431190025802142430837688970305792974078375 / 816367055737193346600670527910237880473747456 *
    μ ^ 7 + 13369440476327688543768300846426611911682373125 /
    19592809337692640318416092669845709131369938944 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r33]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d40, jv_d31, jv_d22, jv_d13, jv_e41, jv_e32, jv_e23,
    jv_e14]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r24 (μ : ℝ) : (jet μ).r24 1 =
    (-40302550951022581459504537796717100470158793 / 289537496123689317441914988618858012463104000 +
    5962010776155954229831184737608488662125827257 / 7527974899215922253489789704090308324040704000
    * μ + 6990945293824729650335132121305124633435437063 /
    1338306648749497289509295947393832590940569600 * μ ^ 2 +
    3343109643776955286945379830667394444614627229157 /
    293892140065389604776241390047685636970549084160 * μ ^ 3 +
    1875430417870073302072631850760227537467307492785 /
    117556856026155841910496556019074254788219633664 * μ ^ 4 +
    34619958652872919711278127737460683332367476275 / 3265468222948773386402682111640951521894989824
    * μ ^ 5 + 73323796853236733711940741316595299214480321275 /
    19592809337692640318416092669845709131369938944 * μ ^ 6 +
    75308566862411237518066629414534597471937931875 /
    19592809337692640318416092669845709131369938944 * μ ^ 7 +
    32870757391755621781213452597568747995091506875 /
    39185618675385280636832185339691418262739877888 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r24]
  rw [jv_c30, jv_c21, jv_c12, jv_c03, jv_d31, jv_d22, jv_d13, jv_e32, jv_e23, jv_e14, jv_e05]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r15 (μ : ℝ) : (jet μ).r15 1 =
    (3472562127440914965868569634527253932259090699 /
    94099686240199028168622371301128854050508800000 - 38469280036068887449363605385699067433989771 /
    940996862401990281686223713011288540505088000 * μ +
    11778248017630663681258787151913808646089080511 / 4014919946248491868527887842181497772821708800
    * μ ^ 2 + 460632023482225811275228816617802441748421948917 /
    73473035016347401194060347511921409242637271040 * μ ^ 3 +
    80488117083872831354173866993907388784446765905 / 9042835078935064762345888924544173445247664128
    * μ ^ 4 + 4854930569357072755650723734789582465705544205 /
    816367055737193346600670527910237880473747456 * μ ^ 5 +
    38698278465070436599588719755876430770538152075 /
    19592809337692640318416092669845709131369938944 * μ ^ 6 -
    110773431354261705438541266455703783640196125 / 376784794955627698431078705189340560218652672 *
    μ ^ 7 + 8453753140462472029142560598252155565787619375 /
    39185618675385280636832185339691418262739877888 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r15]
  rw [jv_c21, jv_c12, jv_c03, jv_d22, jv_d13, jv_e23, jv_e14, jv_e05]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `r06` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_r06 (μ : ℝ) : (jet μ).r06 1 =
    (443931553713954501539471919179870097974974201 / 47049843120099514084311185650564427025254400000
    - 13355960025724686687689300837168320595963953 / 501864993281061483565985980272687221602713600 *
    μ + 150567051878735089404891402385937565906730681 /
    301118995968636890139591588163612332961628160 * μ ^ 2 +
    414223993102641997699041290210528901702386610701 /
    293892140065389604776241390047685636970549084160 * μ ^ 3 +
    16644278191726078622816837221883512043601946813 / 7347303501634740119406034751192140924263727104
    * μ ^ 4 + 4315037001492801847406392852978094695329201995 /
    3265468222948773386402682111640951521894989824 * μ ^ 5 +
    240419645097809661786420128055374368520629925 / 612275291802895009950502895932678410355310592 *
    μ ^ 6 - 4821244956028833454734004665762421548099629125 /
    19592809337692640318416092669845709131369938944 * μ ^ 7 -
    1691311105877763974886679942696772085223390625 / 2449101167211580039802011583730713641421242368
    * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.r06]
  rw [jv_c12, jv_c03, jv_d13, jv_e14, jv_e05]
  simp only [jet]
  ring

/-- The Lyapunov chain of the jet: `f60` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f60 (μ : ℝ) : (jet μ).f60 1 =
    (-368580834982269572678623466092163444548817843 / 4590228597082879422859627868347748978073600000
    - 697442702496718146609174979830019274535353311 / 940996862401990281686223713011288540505088000
    * μ + 2912834709160255302010411046953138240458470033 /
    8029839892496983737055775684362995545643417600 * μ ^ 2 +
    274624660086517455808772561537748758437768129939 /
    146946070032694802388120695023842818485274542080 * μ ^ 3 +
    548704753264416841344515001433026777028823506079 /
    235113712052311683820993112038148509576439267328 * μ ^ 4 +
    7938089665512307328393256464379703976768479265 / 4898202334423160079604023167461427282842484736
    * μ ^ 5 + 139671472120341280416347207553031046866740373375 /
    117556856026155841910496556019074254788219633664 * μ ^ 6 +
    1292664778580833119157354909642046550513436875 / 3265468222948773386402682111640951521894989824
    * μ ^ 7 + 25009692817919656779846025787321059642583764375 /
    235113712052311683820993112038148509576439267328 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f60]
  rw [jv_r51, jv_r33, jv_r15]
  ring

/-- The Lyapunov chain of the jet: `f51` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f51 (μ : ℝ) : (jet μ).f51 1 =
    (-13311557192477723817957857964908328355023665753 /
    188199372480398056337244742602257708101017600000 -
    3177008608042229345581264756039183088513443523 / 2509324966405307417829929901363436108013568000
    * μ - 15191813535725338559698874879334849626662332871 /
    24089519677490951211167327053088986636930252800 * μ ^ 2 -
    705017033402416448532948740933255873422153937 / 7168100977204624506737594879211844804159733760 *
    μ ^ 3 + 210910026967580770689550991284280312823067925111 /
    235113712052311683820993112038148509576439267328 * μ ^ 4 +
    7553639273165736525446849561224674712474301545 / 9796404668846320159208046334922854565684969472
    * μ ^ 5 + 17593157648340332496409244886885736633743550375 /
    39185618675385280636832185339691418262739877888 * μ ^ 6 +
    3881075325462567639613524374552128077950511125 / 19592809337692640318416092669845709131369938944
    * μ ^ 7 - 606228927314261907082680199429329370174721875 /
    6028556719290043174897259283029448963498442752 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f51]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `f42` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f42 (μ : ℝ) : (jet μ).f42 1 =
    (-2370963384128463919177745130304906010117218837 /
    23524921560049757042155592825282213512627200000 - 291050693796572564668752478298349906440807689
    / 376398744960796112674489485204515416202035200 * μ +
    2688379379517284074550671222862200261567899161 / 1003729986562122967131971960545374443205427200
    * μ ^ 2 + 227107257345430863698837178544351118443699443893 /
    36736517508173700597030173755960704621318635520 * μ ^ 3 +
    457528377768179075349123116262477277805303335933 /
    58778428013077920955248278009537127394109816832 * μ ^ 4 +
    6686168897001152681390179992000580601502348305 / 1224550583605790019901005791865356820710621184
    * μ ^ 5 + 4955894727797633987187539456373694351094144175 /
    1632734111474386693201341055820475760947494912 * μ ^ 6 +
    1636059740618001064147869150746692047899921375 / 2449101167211580039802011583730713641421242368
    * μ ^ 7 + 1818599468065846714409238453723230623122499375 /
    6530936445897546772805364223281903043789979648 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f42]
  rw [jv_r33, jv_r15]
  ring

/-- The Lyapunov chain of the jet: `f33` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f33 (μ : ℝ) : (jet μ).f33 1 =
    (-442650572112417735364031775959776421349957947 /
    56459811744119416901173422780677312430305280000 -
    11374863729191410273996473768465372720687954601 /
    11291962348823883380234684556135462486061056000 * μ -
    58475570141160564409115292962718332518605032053 /
    36134279516236426816750990579633479955395379200 * μ ^ 2 -
    737725776892644807053133265133182616350454324789 /
    440838210098084407164362085071528455455823626240 * μ ^ 3 +
    361877208342728223560258415184820527232537239549 /
    352670568078467525731489668057222764364658900992 * μ ^ 4 +
    791321611787291768986803948514707738059954695 / 1632734111474386693201341055820475760947494912 *
    μ ^ 5 + 17934902933429595192414450813296132640538495175 /
    58778428013077920955248278009537127394109816832 * μ ^ 6 -
    3569884335238774488288612437396593337916975875 / 29389214006538960477624139004768563697054908416
    * μ ^ 7 - 19974911308238934691598446606832773986254226875 /
    39185618675385280636832185339691418262739877888 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f33]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `f24` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f24 (μ : ℝ) : (jet μ).f24 1 =
    (3472562127440914965868569634527253932259090699 /
    188199372480398056337244742602257708101017600000 - 38469280036068887449363605385699067433989771
    / 1881993724803980563372447426022577081010176000 * μ +
    11778248017630663681258787151913808646089080511 / 8029839892496983737055775684362995545643417600
    * μ ^ 2 + 460632023482225811275228816617802441748421948917 /
    146946070032694802388120695023842818485274542080 * μ ^ 3 +
    80488117083872831354173866993907388784446765905 /
    18085670157870129524691777849088346890495328256 * μ ^ 4 +
    4854930569357072755650723734789582465705544205 / 1632734111474386693201341055820475760947494912
    * μ ^ 5 + 38698278465070436599588719755876430770538152075 /
    39185618675385280636832185339691418262739877888 * μ ^ 6 -
    110773431354261705438541266455703783640196125 / 753569589911255396862157410378681120437305344 *
    μ ^ 7 + 8453753140462472029142560598252155565787619375 /
    78371237350770561273664370679382836525479755776 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f24]
  rw [jv_r15]
  ring

/-- The Lyapunov chain of the jet: `f15` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_f15 (μ : ℝ) : (jet μ).f15 1 =
    (3387166380200994326688911854803349033475415799 /
    188199372480398056337244742602257708101017600000 -
    1221364851487349403282089617175492022096671431 / 2509324966405307417829929901363436108013568000
    * μ - 1033260315601349205335445137681519463107162839 /
    963580787099638048446693082123559465477210112 * μ ^ 2 -
    446986152281789863494315311287771621526047005829 /
    293892140065389604776241390047685636970549084160 * μ ^ 3 -
    178656964081123326154291312231249608035469201553 /
    235113712052311683820993112038148509576439267328 * μ ^ 4 -
    2115864747208845444392265685929769102252517765 / 3265468222948773386402682111640951521894989824
    * μ ^ 5 - 8077151997604352747007489552495806798990338325 /
    39185618675385280636832185339691418262739877888 * μ ^ 6 -
    12114008800121910857355733535826881099008846375 /
    19592809337692640318416092669845709131369938944 * μ ^ 7 -
    43494606099651274162642357416878032511144234375 /
    78371237350770561273664370679382836525479755776 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.f15]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `k6` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_k6 (μ : ℝ) : (jet μ).k6 1 =
    (-49651834665573530248138257496462999 / 5798815449383936324552003376619520000 +
    800441440197902557159578425834790097 / 1739644634815180897365601012985856000 * μ +
    3501196436529492580224040200333373673 / 2226745132563431548627969296621895680 * μ ^ 2 +
    652516769901485199457460122614511019 / 222674513256343154862796929662189568 * μ ^ 3 +
    109579161444548701005528027710603074769 / 36221720823031819857681633891716169728 * μ ^ 4 +
    557295481550304787016137867746809365 / 282982193929936092638137764779032576 * μ ^ 5 +
    793509252603121827436526900773152725 / 1325184908159700726500547581404250112 * μ ^ 6 +
    1685289558506903963504452368394525875 / 4527715102878977482210204236464521216 * μ ^ 7 -
    14735286516852435428454113733500890625 / 108665162469095459573044901675148509184 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.k6]
  rw [jv_r60, jv_r42, jv_r24, jv_r06]
  ring

/-- The Lyapunov chain of the jet: `l2` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jv_l2 (μ : ℝ) : (jet μ).l2 1 =
    (-49651834665573530248138257496462999 / 2899407724691968162276001688309760000 +
    800441440197902557159578425834790097 / 869822317407590448682800506492928000 * μ +
    3501196436529492580224040200333373673 / 1113372566281715774313984648310947840 * μ ^ 2 +
    652516769901485199457460122614511019 / 111337256628171577431398464831094784 * μ ^ 3 +
    109579161444548701005528027710603074769 / 18110860411515909928840816945858084864 * μ ^ 4 +
    557295481550304787016137867746809365 / 141491096964968046319068882389516288 * μ ^ 5 +
    793509252603121827436526900773152725 / 662592454079850363250273790702125056 * μ ^ 6 +
    1685289558506903963504452368394525875 / 2263857551439488741105102118232260608 * μ ^ 7 -
    14735286516852435428454113733500890625 / 54332581234547729786522450837574254592 * μ ^ 8) := by
  simp only [PlanarFocus.Jet5.l2]
  rw [jv_k6]
  ring

/-! ## The Bautin point of the path -/

/-- **The Bautin quartic** of the path: `l₁(J) = −𝔔(μ)/774416364800`,
`hopfNum = −𝔔(μ)/44306691200`. -/
def bautinQuartic (μ : ℝ) : ℝ :=
  139686596875 * μ ^ 4 + 137026829625 * μ ^ 3 + 340370963275 * μ ^ 2 + 339387544335 * μ -
    25044421202

/-- `l₁(J) = −𝔔(μ)/774416364800` along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1 (μ : ℝ) :
    (jet μ).l1 1 = -bautinQuartic μ / 774416364800 := by
  rw [jv_l1, bautinQuartic]; ring

/-- The integer numerator of `l₂(J)` (coefficients from the constant term up). -/
def l2Num : List ℤ := [-581522287603197186266195271798574644288,
    31249233825326115831509941744590205386880, 106786491314149523696833226110167897026500,
    199017614819952985834525337397425860795000, 205460927708528814385365051957380765191875,
    133750915572073148883873088259234247600000, 40667349195909993656122003664624077156250,
    25279343377603559452566785525917888125000, -9209554073032772142783821083438056640625]

/-- `l₂(J) = l2Num(μ)/l2Den` along the path. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l2 (μ : ℝ) :
    (jet μ).l2 1 = zeval l2Num μ / 33957863271592331116576531773483909120000 := by
  rw [jv_l2]
  simp only [l2Num, zeval]
  push_cast
  ring

/-- **`l₂ > 0` on `[6/100, 7/100)`** (a Möbius sign certificate, `decide +kernel`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem l2Num_pos {μ : ℝ} (h1 : 6 / 100 ≤ μ) (h2 : μ < 7 / 100) :
    0 < zeval l2Num μ :=
  zeval_pos_of_zmob_Ico (A := 6) (B := 7) (C := 100) (by norm_num) (by decide +kernel)
    (by push_cast; linarith) (by push_cast; linarith)

/-- **The positive roots of the Bautin quartic lie in `(6/100, 7/100)`** (`𝔔` increases on
`μ ≥ 0`, `𝔔(6/100) < 0 < 𝔔(7/100)`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bautinQuartic_root_mem {μ : ℝ} (hμ : 0 < μ)
    (hq : bautinQuartic μ = 0) : 6 / 100 < μ ∧ μ < 7 / 100 := by
  unfold bautinQuartic at hq
  constructor
  · by_contra h
    push Not at h
    have e2 : μ ^ 2 ≤ (6 / 100) ^ 2 := pow_le_pow_left₀ hμ.le h 2
    have e3 : μ ^ 3 ≤ (6 / 100) ^ 3 := pow_le_pow_left₀ hμ.le h 3
    have e4 : μ ^ 4 ≤ (6 / 100) ^ 4 := pow_le_pow_left₀ hμ.le h 4
    nlinarith
  · by_contra h
    push Not at h
    have e2 : (7 / 100) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
    have e3 : (7 / 100) ^ 3 ≤ μ ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    have e4 : (7 / 100) ^ 4 ≤ μ ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    nlinarith

/-- **The path has a Bautin point**: the quartic has a root in `(6/100, 7/100)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_bautinQuartic_root :
    ∃ μ : ℝ, 6 / 100 < μ ∧ μ < 7 / 100 ∧ bautinQuartic μ = 0 := by
  have hc : ContinuousOn bautinQuartic (Set.Icc (6 / 100) (7 / 100)) := by
    unfold bautinQuartic; fun_prop
  have h := intermediate_value_Ioo (by norm_num : (6 / 100 : ℝ) ≤ 7 / 100) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo (bautinQuartic (6 / 100)) (bautinQuartic (7 / 100)) := by
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

/-- **The first Lyapunov numerator of the path**: `hopfNum = −𝔔(μ)/44306691200` (the data
`M = 85/122`, `D = 10/61`, `ω_q = 1`, `ω = 1`, `K_t = 6/5`, `Q_tδ = −1`, `n_q/E* = μ`,
`ρ = 7/8`, `τ = 7/16`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem bpath_hopfNumAt (hμ : 0 < μ) :
    (bpath μ).hopfNumAt = -bautinQuartic μ / 44306691200 := by
  obtain ⟨-, -, h3, h4, h5, h6⟩ := bpath_data hμ
  rw [Model.hopfNumAt, bpath_hopfFreq hμ, bpath_emf, show (bpath μ).δ = 0 from rfl, h3, h4, h5, h6,
    show (bpath μ).q.ωq = 1 from rfl, show (bpath μ).q.M = 85 / 122 from rfl,
    show (bpath μ).q.D = 10 / 61 from rfl, show (bpath μ).q.nq = μ from rfl, div_one]
  simp only [hopfNum, hopfNum1, hopfNum2, hopfNum3, bautinQuartic]
  ring

end Bautin

open Bautin

/-- **The Bautin point of the path is unstable**: at a positive root of the Bautin quartic
(`ℓ₁ = 0`; the root lies in `(6/100, 7/100)` and exists, `Bautin.exists_bautinQuartic_root`),
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
      G0, QVDroop.Bautin.pv]
    ring_nf
  · refine ((G1_sub_jet hμ).trans_isLittleO
      (Dynamics.isLittleO_pow_of_tendsto tendsto_norm0 (by norm_num : 5 < 6))).congr_left
      fun y => ?_
    rw [show (fun x => (bpath μ).field x - fderiv ℝ (bpath μ).field 0 x) = fnl μ from rfl,
      chartField_eq hμ, jetG_eq]
    simp only [PlanarFocus.frameX_apply, PlanarFocus.frameY_apply, PiLp.add_apply, rotL_apply0,
      rotL_apply1, G1, QVDroop.Bautin.pv]
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

end QVDroopVirtual
end powerlib.GFM
