import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.GridTiedConverter.GFM.VSMLPFLossy
import theorem.Criteria.Routh5

/-! # The VSM with a power filter on a dynamic line: quintic family, filter, fast-line limit

The five-state VSM + power filter (droop + LPF) of
`theorem/GridTiedConverter/GFM/Line/Model.lean` linearized at its operating point: its
characteristic polynomial from the `fderiv` Jacobian, its quintic Routh–Hurwitz conditions as the
model family `Line.VSMLPF.family`, the sum and product rules against the reduced three-state
model, and the comparison with the quasi-static (phasor) reduction, the lossy three-state family
`GFM.VSMLPFLossy.family` (`theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`): the reduced model can
be stable while the full model is unstable. Then the power filter of the reduced model as a
second time scale: the values of the reduced characteristic cubic at `−ω_c`, `−D/M` and
`−(ω_c + D/M)`, and the location of its real root. Last, the fast-line limit of the four-state
VSM on the line (`Line.VSM.family`): its exact boundary in the damping is `D_line (1 + O(ε²))`.

Model boundary.
* State `(δ, ω, P_f, i_d, i_q) : State 5`, grid dq frame at `ω₀`, export-positive active power,
  the field `Line.VSMLPF.field` (`δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P_e − P_f)`,
  `L i̇ = E e^{jδ} − V − (R + jX) i`); its boundary is that of
  `theorem/GridTiedConverter/GFM/Line/Model.lean` (constant `E`, R–L line, no inner loops, PLL,
  delay, PWM, LC filter).
* A model `Line.VSMLPF.Model` is a parameter set with a selected angle `δ*`, read at the operating
  point `(δ*, 0, P_ref, i_s(δ*))`; `Q = Q(δ*)`, `K = K(δ*) = P'(δ*)`, `σ = R/L`,
  `ρ = σ² + (X/L)²`. Its quasi-static reduction is the lossy three-state model `GFM.VSMLPFLossy`
  of the same data about the same angle (`VSMLPF.Model.toLossy`); on a lossless line the
  three-state `GFM.VSMLPF` of `theorem/GridTiedConverter/GFM/VSMLPF.lean` with `K = K₀ cos δ`.
* The last section reads four-state models `Line.VSM.Model` (field `Line.VSM.field`, boundary of
  `theorem/GridTiedConverter/GFM/Line/VSM.lean`) on lines of time scale `ε = 1/ω₀` with `E, V, R`,
  the reactance `X` (hence the power curve, `K`, `Q`) and the set-point fixed: `L = ε X`,
  `ω₀ = 1/ε` (`VSM.Model.atScale`); `ε → 0⁺` only, for `R, X, M > 0`, `E ≠ 0`, `K > 0`.
* Level: local exponential stability / instability of the operating point by linearization
  (Routh–Hurwitz, degrees five and four) and its converse; static evidence on the reduced model
  (filter limits); the first two orders of the four-state boundary (`Asymptotics.IsBigO`); no
  global or transient claim.

Source: study note `gfm/t4-timescale/REPORT.md` ("Exact linear structure", (c) mechanisms 1 and
3, (d)) and its scripts `t4_02_charpoly.py`, `t4_04_vsm_boundary.py`, `t4_06_lpf_boundary.py`,
`t4_07_filter_timescale.py` (discovery evidence only); the quintic Routh–Hurwitz criterion
(`theorem/Criteria/Routh5.lean`). Scaffold of the comparison with the reduced model:
`theorem/GridTiedConverter/GFM/Line/LineReduction.agda`.

Results.
* `VSMLPF.det_characteristicMatrix`, `VSMLPF.characteristic_polynomial`: at every state
  `M det(sI − J) = (M s³ + (D + M ω_c) s² + D ω_c s − ω_c Q_e)(s² + 2σ s + ρ) + ω_c E² X/L²`;
  expanded (`VSMLPF.det_characteristicMatrix_quintic`) the monic quintic with coefficients
  `a₄ = 2σ + D/M + ω_c`, `a₃ = ρ + 2σ (D/M + ω_c) + D ω_c/M`,
  `a₂ = (D/M + ω_c) ρ + 2σ D ω_c/M − ω_c Q/M` and `a₁`, `a₀` equal to `ω_c` times those of the
  four-state model (`VSMLPF.coeff4` … `VSMLPF.coeff0`); at the operating point
  (`VSMLPF.Model.det_characteristicMatrix`) `a₀ = ω_c ρ K/M` (`VSMLPF.Model.coeff0_eq`).
* Sum and product rules (`VSMLPF.Model.trace_jac`, `VSMLPF.Model.det_jac`): the trace and the
  determinant of the five-state Jacobian at the operating point are those of the reduced
  three-state Jacobian (`GFM.VSMLPF.jacobian` of the lossless parameters at `δ* − α`) and of the
  uncoupled line block, added and multiplied.
* `VSMLPF.reducedField_eq_lossy`: the slow rows on the quasi-steady set are the lossy three-state
  field `GFM.VSMLPFLossy ⟨M, D, ω_c, P_ref, c₀, A, α⟩` (lossless line:
  `VSMLPF.reducedField_eq_vsmlpf` of the model module).
* Filter limits of the reduced model (`filter_charPoly_values`):
  `p(−ω_c) = p(−D/M) = ω_c K`, `p(−(ω_c + D/M)) = ω_c (K − D ω_c − D²/M)` for
  `p(s) = M det(sI − J)`; hence (`filter_real_root`) for `M, D, ω_c, K > 0` and the stable side
  `K < D ω_c + D²/M` the cubic has a real root `λ ∈ (−(ω_c + D/M), −max(ω_c, D/M))` (faster than
  both limits) and the complementary pair has real-part sum `−b` with `0 < b < min(ω_c, D/M)`:
  the slow pair is less damped than both limits (swing `ω_c → ∞`, droop + LPF `M → 0`).
* Fast-line limit of the four-state boundary: with `D_line(ε) = ε · 2 E² R X²/|Z|⁴`
  (`VSM.Model.DlineAt`, the line damping of the scaled model, `VSM.Model.atScale_Dline`) there
  are `C, ε₀ > 0` such that for `ε ∈ (0, ε₀)` every damping `D ≥ D_line(ε)(1 + C ε²)` meets the
  quartic Routh conditions and every positive `D ≤ D_line(ε)(1 − C ε²)` strictly violates them
  (`VSM.Model.exists_routh_sandwich`); hence the critical damping `VSM.Model.Dcrit` (infimum of
  the positive dampings meeting them) has `D_crit/D_line − 1 = O(ε²)` as `ε → 0⁺`
  (`VSM.Model.isBigO_Dcrit`).
* Second order of the fast-line limit: with the study's coefficient
  `c₂ = 2 (K/M)(1 − r²)/(1 + r²)²`, `r = R/X` (`VSM.Model.DcritCoeff`), every positive
  `D ≥ D_line(ε)(1 + c₂ ε² + C ε⁴)` meets the quartic Routh conditions and every positive
  `D ≤ D_line(ε)(1 + c₂ ε² − C ε⁴)` strictly violates them for `ε ∈ (0, ε₀)`
  (`VSM.Model.exists_routh_sandwich_two`; the first-order sandwich is its corollary), so
  `D_crit/D_line − 1 − c₂ ε² = O(ε⁴)` (`VSM.Model.isBigO_Dcrit_sub`): on a fast line the
  critical damping exceeds `D_line` when `R < X` and falls below it when `R > X`.
* Hopf points of the five-state model (`theorem/GridTiedConverter/GFM/HopfLineLPF.lean`): the
  family laws `VSMLPF.mem_den_unstable_of_firstLyapunov_pos`,
  `VSMLPF.mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`, a supercritical and a
  subcritical witness and the non-exactness of the local asymptotic and instability translations.
  On the zero-current slice `δ* = 0`, `V = E`: the closed form of `ℓ₁`, its sign law and the
  complete local asymptotic membership (`theorem/GridTiedConverter/GFM/HopfLineLPFSlice.lean`).
  Not decided: a closed form of `ℓ₁` for all parameters (the exact real-part numerator in the
  frame rotated with `δ*` has thousands of terms before the Gröbner reduction modulo the two
  frequency relations; the four-state and the PSC laws are in
  `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean` and
  `theorem/GridTiedConverter/GFM/HopfLinePSC.lean`).
* The fold `K = 0` of the five-state model (`theorem/GridTiedConverter/GFM/LineVSMLPFFold.lean`):
  the null pair, the fold coefficient `(P(δ*) − c₀)/(2 (D − D_line))` (nonzero off
  `D = D_line`), `det(sI − J) = s (s⁴ + a₄ s³ + a₃ s² + a₂ s + a₁)` and the degenerate fold
  points (the Bogdanov–Takens damping `a₁ = 0` and the zero–Hopf points `Δ₃ = 0`).
* Hopf cycles along the damping and the inverse inertia
  (`theorem/GridTiedConverter/GFM/LineVSMLPFHopfCycle.lean`): both families, their transversality
  coefficients in closed form on the zero-current slice (`sign τ_D = −sign 𝔗`, no fixed sign;
  `sign τ_M = sign 𝔍`; never both zero) and at both witnesses; the cycles at every slice Hopf
  point with `ℓ₁ ≠ 0` are private evidence (uniqueness and orbital stability not proved).

Family and connection conclusions.
* `Line.VSMLPF.family`: static requirements `balanced` (`P(δ*) = P_ref`), `physical`
  (`Network.Physical`, `M, D, ω_c > 0`), `routh` (the quintic Routh–Hurwitz conditions
  `Criteria.QuinticRouth`, Hurwitz determinants `Δ₁, …, Δ₅ > 0`, of the monic characteristic
  polynomial at the operating point) and `destabilizing` (their strict violation
  `Criteria.QuinticRouthViolation`). The local sentences translate into
  `{balanced, physical, routh}`, instability into `{balanced, physical, destabilizing}`, passivity
  into nothing (exact), the remaining sentences into the whole, inconsistent, language
  (`VSMLPF.realize_univ`); `VSMLPF.chain_le_semantics` proves soundness
  (`VSMLPF.mem_den_locallyExponentiallyStable`, `VSMLPF.mem_den_unstable`). Within `physical` the
  local exponential translation is exact (`VSMLPF.exactUnder_locallyExponentiallyStable`,
  converse linearization).
* `VSMLPF.mem_den_locallyExponentiallyStable_iff`: the exact boundary, for a balanced physical
  model: local exponential stability iff `K > 0` and `Δ₂, Δ₃, Δ₄ > 0` (`Δ₁ = a₄ > 0` always,
  `Δ₅ = a₀ Δ₄`). `VSMLPF.mem_den_unstable_of_K_neg`: `K < 0` makes `a₀ = ω_c ρ K/M` negative,
  so the full model is unstable whenever its reduction is a saddle. At the fold `K = 0`
  (`theorem/GridTiedConverter/GFM/LineVSMLPFFold.lean`): `VSMLPF.mem_den_unstable_of_fold` and
  `VSMLPF.mem_den_unstable_of_fold_of_ne` (unstable for `a₁ ≠ 0`, `Δ₃ ≠ 0`: a saddle-node).
* The phasor model is stable but the full model unstable (connection of `Line.VSMLPF.family` and
  `GFM.VSMLPFLossy.family` through `VSMLPF.Model.toLossy`, scaffold
  `theorem/GridTiedConverter/GFM/Line/LineReduction.agda`): every balanced physical model whose
  reduction meets `0 < K < D ω_c + D²/M` and whose quintic conditions are strictly violated
  (`VSMLPF.lossy_stable_full_unstable_of_violation`). On the lossy line
  `E = V = R = L = ω₀ = M = ω_c = 1` at zero load the boundary witnesses `VSMLPF.lowDamping`
  (`D = 1/2`: reduced stable, full unstable with `Δ₄ = −233/8`,
  `VSMLPF.lowDamping_lossy_stable_full_unstable`) and `VSMLPF.highDamping` (`D = 1`: the full model
  stable, `VSMLPF.highDamping_stable`).
* Four-state fast-line limit (in `Line.VSM.family`, `VSM.Model.atScale_mem_den_sandwich`): for a
  balanced physical model with `R > 0` and `K > 0`, on every line of time scale `ε ∈ (0, ε₀)` the
  model is locally exponentially stable for `D ≥ D_line(ε)(1 + C ε²)` and unstable for positive
  `D ≤ D_line(ε)(1 − C ε²)` (its swing reduction is stable for every `D > 0`,
  `Synchronous.Swing.mem_den_locallyExponentiallyStable`).
-/
noncomputable section
namespace powerlib.GFM.Line
open powerlib.Dynamics (State)
open Set

namespace VSMLPF

variable (g : VSMLPF)

/-! ## The five-state characteristic polynomial -/

/-- The monic characteristic polynomial of the Jacobian at any state, in product form. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (δ id iq : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      (s ^ 3 + ((g.D / g.M + g.ωc : ℝ) : ℂ) * s ^ 2 + ((g.D * g.ωc / g.M : ℝ) : ℂ) * s -
          ((g.ωc * g.reactive δ id iq / g.M : ℝ) : ℂ)) *
        (s ^ 2 + ((2 * g.σ : ℝ) : ℂ) * s + (g.ρ : ℂ)) +
          ((g.ωc * g.E ^ 2 * g.X / (g.L ^ 2 * g.M) : ℝ) : ℂ) := by
  simp only [Linear.characteristicMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  simp [jacobian, Linear.complexify, Fin.succAbove, Fin.lt_def, Network.ρ,
    Network.σ]
  linear_combination ((g.ωc : ℂ) * (g.E : ℂ) ^ 2 * (g.X : ℂ) / ((g.L : ℂ) ^ 2 * (g.M : ℂ))) *
    Complex.sin_sq_add_cos_sq (δ : ℂ)

/-- **Characteristic polynomial**: at every state
`M det(sI − J) = (M s³ + (D + M ω_c) s² + D ω_c s − ω_c Q_e)(s² + 2σ s + ρ) + ω_c E² X/L²`. -/
@[tmio M, powerlib_domain] theorem characteristic_polynomial (hM : g.M ≠ 0) (δ id iq : ℝ)
    (s : ℂ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      ((g.M : ℂ) * s ^ 3 + ((g.D + g.M * g.ωc : ℝ) : ℂ) * s ^ 2 + ((g.D * g.ωc : ℝ) : ℂ) * s -
          ((g.ωc * g.reactive δ id iq : ℝ) : ℂ)) *
        (s ^ 2 + ((2 * g.σ : ℝ) : ℂ) * s + (g.ρ : ℂ)) +
          ((g.ωc * g.E ^ 2 * g.X / g.L ^ 2 : ℝ) : ℂ) := by
  rw [det_characteristicMatrix]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp

@[tmio M, powerlib_domain] private theorem trace_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).trace = -(g.D / g.M + g.ωc) - 2 * g.σ := by
  simp [jacobian, Matrix.trace, Fin.sum_univ_five, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem det_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).det =
      -((g.ωc * g.E ^ 2 * g.X / (g.L ^ 2 * g.M)) - g.ωc * g.reactive δ id iq / g.M * g.ρ) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply]
  simp [jacobian, Fin.succAbove, Fin.lt_def, Network.ρ, Network.σ]
  linear_combination (-(g.ωc * g.E ^ 2 * g.X / (g.L ^ 2 * g.M))) * Real.sin_sq_add_cos_sq δ

/-! ## Models at the operating point -/

/-- The lossy three-state parameters of the quasi-static reduction. -/
def toLossy : powerlib.GFM.VSMLPFLossy := ⟨g.M, g.D, g.ωc, g.Pref, g.c0, g.A, g.α⟩

/-- **Quasi-static reduction**: the slow rows on the quasi-steady set are the lossy three-state
field `GFM.VSMLPFLossy ⟨M, D, ω_c, P_ref, c₀, A, α⟩`. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_lossy (hZ : 0 < g.absSq) :
    g.reducedField = g.toLossy.field := by
  funext y
  ext i
  fin_cases i
  · simp [reducedField, qss, powerlib.GFM.VSMLPFLossy.field, toLossy]
  · simp [reducedField, qss, powerlib.GFM.VSMLPFLossy.field, toLossy]
  · have hP := g.qssPower_eq_polar hZ (y 0)
    show g.ωc * (g.power (y 0) (g.is (y 0)).re (g.is (y 0)).im - y 2) =
      g.ωc * (g.c0 + g.A * Real.sin (y 0 - g.α) - y 2)
    rw [← hP]; rfl

/-- The Jacobian at the operating point `(δ*, 0, P_ref, i_s(δ*))`. -/
def Model.jac (m : Model) : Matrix (Fin 5) (Fin 5) ℝ :=
  m.g.jacobian m.δ (m.g.is m.δ).re (m.g.is m.δ).im

/-- The reduced three-state Jacobian: the lossless `GFM.VSMLPF` Jacobian of the reading of the
lossy model at `δ* − α`. -/
def Model.reducedJac (m : Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  m.g.toLossy.toVSMLPF.jacobian (m.δ - m.g.α)

/-- **Sum rule**: `tr J = tr J_reduced + tr J_line`. -/
@[tmio M, powerlib_domain] theorem Model.trace_jac (m : Model) :
    m.jac.trace = m.reducedJac.trace + m.g.lineJacobian.trace := by
  rw [Model.jac, trace_jacobian, Model.reducedJac, powerlib.GFM.VSMLPF.trace_jacobian,
    Network.trace_lineJacobian]
  simp [toLossy, powerlib.GFM.VSMLPFLossy.toVSMLPF]; ring

/-- **Product rule**: `det J = det J_reduced · det J_line` (`L ≠ 0`, `|Z|² > 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_jac (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.jac.det = m.reducedJac.det * m.g.lineJacobian.det := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  have h2 := m.g.κ_mul_ρ hL hZ.ne'
  rw [Model.jac, det_jacobian, Model.reducedJac, powerlib.GFM.VSMLPF.det_jacobian,
    Network.det_lineJacobian]
  simp only [toLossy, powerlib.GFM.VSMLPFLossy.toVSMLPF]
  have hK : m.g.A * Real.cos (m.δ - m.g.α) = m.g.κ - m.g.qssReactive m.δ := by
    rw [← h1, Network.syncCoeff]; ring
  change _ = -(m.g.ωc * (m.g.A * Real.cos (m.δ - m.g.α))) / m.g.M * m.g.ρ
  rw [hK, show m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.qssReactive m.δ from rfl]
  have e : m.g.ωc * m.g.E ^ 2 * m.g.X / (m.g.L ^ 2 * m.g.M) = m.g.ωc * (m.g.κ * m.g.ρ) / m.g.M :=
    by rw [h2]; ring
  rw [e]; ring

/-! ## The quintic at the operating point -/

/-- Monic coefficient of `s⁴`: `a₄ = 2σ + D/M + ω_c`. -/
def coeff4 : ℝ := 2 * g.σ + (g.D / g.M + g.ωc)

/-- Monic coefficient of `s³`: `a₃ = ρ + 2σ (D/M + ω_c) + D ω_c/M`. -/
def coeff3 : ℝ := g.ρ + 2 * g.σ * (g.D / g.M + g.ωc) + g.D * g.ωc / g.M

/-- Monic coefficient of `s²` at reactive power `Q`: `a₂ = (D/M + ω_c) ρ + 2σ D ω_c/M − ω_c Q/M`.
-/
def coeff2 (Q : ℝ) : ℝ :=
  (g.D / g.M + g.ωc) * g.ρ + 2 * g.σ * (g.D * g.ωc / g.M) - g.ωc * Q / g.M

/-- Monic coefficient of `s` at reactive power `Q`: `a₁ = ω_c (Dρ − 2σQ)/M`, `ω_c` times that of
the four-state model (`VSM.coeff1`). -/
def coeff1 (Q : ℝ) : ℝ := g.ωc * g.toVSM.coeff1 Q

/-- Monic constant coefficient at reactive power `Q`: `a₀ = ω_c (E² X/L² − Qρ)/M`, `ω_c` times that
of the four-state model (`VSM.coeff0`). -/
def coeff0 (Q : ℝ) : ℝ := g.ωc * g.toVSM.coeff0 Q

/-- The monic characteristic polynomial of the Jacobian at any state, expanded:
`s⁵ + a₄ s⁴ + a₃ s³ + a₂(Q_e) s² + a₁(Q_e) s + a₀(Q_e)`. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_quintic (δ id iq : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      s ^ 5 + (g.coeff4 : ℂ) * s ^ 4 + (g.coeff3 : ℂ) * s ^ 3 +
        (g.coeff2 (g.reactive δ id iq) : ℂ) * s ^ 2 + (g.coeff1 (g.reactive δ id iq) : ℂ) * s +
          (g.coeff0 (g.reactive δ id iq) : ℂ) := by
  rw [det_characteristicMatrix]
  simp only [coeff4, coeff3, coeff2, coeff1, coeff0, VSM.coeff1, VSM.coeff0]
  push_cast
  ring

/-- Reactive power `Q = Q(δ*)` at the operating point. -/
def Model.Q (m : Model) : ℝ := m.g.qssReactive m.δ

/-- Synchronizing coefficient `K = P'(δ*) = A cos(δ* − α)` at the operating point. -/
def Model.K (m : Model) : ℝ := m.g.syncCoeff m.δ

@[tmio M, powerlib_domain] theorem Model.fderiv_point (m : Model) :
    fderiv ℝ m.g.field m.point = Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac := by
  rw [m.g.fderiv_field]
  simp [Model.point, qss, Model.jac]

/-- The monic characteristic polynomial at the operating point. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix (m : Model) (s : ℂ) :
    (Linear.characteristicMatrix m.jac s).det =
      s ^ 5 + (m.g.coeff4 : ℂ) * s ^ 4 + (m.g.coeff3 : ℂ) * s ^ 3 + (m.g.coeff2 m.Q : ℂ) * s ^ 2 +
        (m.g.coeff1 m.Q : ℂ) * s + (m.g.coeff0 m.Q : ℂ) :=
  m.g.det_characteristicMatrix_quintic _ _ _ s

/-- At the operating point the constant coefficient is `ω_c ρ K/M`
(`VSM.Model.coeff0_eq` of the four-state model with the same data). -/
@[tmio M, powerlib_domain] theorem Model.coeff0_eq (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) : m.g.coeff0 m.Q = m.g.ωc * (m.g.ρ * m.K / m.g.M) := by
  have h := VSM.Model.coeff0_eq ⟨m.g.toVSM, m.δ⟩ hL hZ
  rw [coeff0]
  exact congrArg (m.g.ωc * ·) h

/-! ## The family -/

/-- Static requirements on VSM + power-filter models on the line. -/
inductive Requirement
  /-- Power balance at the selected angle: `P(δ*) = P_ref`. -/
  | balanced
  /-- Physical network (`Network.Physical`), positive inertia, damping and filter bandwidth. -/
  | physical
  /-- The quintic Routh–Hurwitz conditions of the monic characteristic polynomial at the
  operating point. -/
  | routh
  /-- A strict violation of a quintic Routh–Hurwitz sign condition. -/
  | destabilizing

/-- The quintic Routh–Hurwitz conditions `Δ₁, …, Δ₅ > 0` at the operating point. -/
def Model.Routh (m : Model) : Prop :=
  Criteria.QuinticRouth m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q) (m.g.coeff0 m.Q)

/-- Their strict violation: a negative coefficient or a negative Hurwitz determinant
`Δ₂`, `Δ₃`, `Δ₄`. -/
def Model.RouthViolation (m : Model) : Prop :=
  Criteria.QuinticRouthViolation m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
    (m.g.coeff0 m.Q)

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.g.qssPower m.δ = m.g.Pref
  | .physical => m.g.Physical ∧ 0 < m.g.M ∧ 0 < m.g.D ∧ 0 < m.g.ωc
  | .routh => m.Routh
  | .destabilizing => m.RouthViolation

/-- The translation of the sentences: the local ones into balance, physical parameters and the
Routh conditions; instability into balance, physical parameters and a strict violation;
passivity into nothing; every other sentence into the whole, inconsistent, language. -/
abbrev translate : Sentence → Set Requirement :=
  Spectral.localTable {.balanced, .physical, .routh} {.balanced, .physical, .routh}
    {.balanced, .physical, .destabilizing} ∅

/-- The VSM + power-filter-on-line family. -/
def family : Family Model Requirement 5 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.g.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.g.field) (pt := Model.point)
    family_isAutonomous

@[tmio M, powerlib_domain] private theorem equilibrium_of {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.g.field m.point = 0 :=
  (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb

/-- Balance, physical parameters and the quintic Routh conditions place a model in local
exponential stability (the Jacobian at the operating point is Hurwitz,
`Criteria.isHurwitz_iff_of_det_characteristicMatrix_quintic`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hr : m.Routh) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact hurwitz_linearization_locally_exponentially_stable m.jac m.g.contDiff_field
    (equilibrium_of hp hb) m.fderiv_point
    ((Criteria.isHurwitz_iff_of_det_characteristicMatrix_quintic _
      m.det_characteristicMatrix).mpr hr)

/-- Balance, physical parameters and a strict quintic Routh violation place a model in
instability (a characteristic root in the open right half plane). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hv : m.RouthViolation) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact unstable_of_exists_complex_eigenvalue_re_pos m.jac m.g.contDiff_field
    (equilibrium_of hp hb) m.fderiv_point
    (Criteria.exists_eigenvalue_re_pos_of_det_characteristicMatrix_quintic_violation _
      m.det_characteristicMatrix hv)

/-- The whole requirement language is inconsistent: the quintic Routh conditions exclude their
strict violation (`Criteria.not_quinticRouthViolation_of_quinticRouth`). -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of_forall fun m h =>
    Criteria.not_quinticRouthViolation_of_quinticRouth (h .routh) (h .destabilizing)

/-- Every translation of the VSM + power-filter-on-line family is sound: the quintic Routh
conditions prove the local sentences, a strict violation proves instability, and passivity holds
without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (fun _ => rfl) realize_univ
    (fun m hm => ?_) (fun m hm => ?_) family_isAutonomous.den_passive
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact mem_den_locallyExponentiallyStable m (hm .physical (by simp))
      (hm .balanced (by simp)) (hm .routh (by simp))
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact mem_den_unstable m (hm .physical (by simp)) (hm .balanced (by simp))
      (hm .destabilizing (by simp))

/-- Within physical parameters the local exponential translation is exact: local exponential
stability of the operating point forces an equilibrium (a balanced angle) whose Jacobian is
Hurwitz, i.e. meets the quintic Routh conditions (converse linearization). -/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.physical} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_les_of_jacobian (fun m P => mem_den_flow_iff) {.physical}
    Model.jac (fun m _ hm => ?_) (fun m _ => m.g.contDiff_field) (fun m _ => m.fderiv_point)
    fun m hI heq hH => ?_
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact mem_den_locallyExponentiallyStable m
      (hm .physical (by simp [family, translate, Spectral.table]))
      (hm .balanced (by simp [family, translate, Spectral.table]))
      (hm .routh (by simp [family, translate, Spectral.table]))
  have hp : Meets m .physical := (TMIO.mem_realize _ _ _).mp hI .physical rfl
  have hb : Meets m .balanced :=
    (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mp heq
  have hr : m.Routh :=
    (Criteria.isHurwitz_iff_of_det_characteristicMatrix_quintic _ m.det_characteristicMatrix).mp hH
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl | rfl)
  · exact hb
  · exact hp
  · exact hr

/-! ## The exact Routh boundary -/

@[tmio M, powerlib_domain] private theorem ρ_pos {m : Model} (hp : Meets m .physical) :
    0 < m.g.ρ := by
  have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hp.1.L.ne']
  rw [this]; exact div_pos hp.1.absSq_pos (pow_pos hp.1.L 2)

@[tmio M, powerlib_domain] private theorem routh_iff {m : Model} (hp : Meets m .physical) :
    m.Routh ↔ 0 < m.K ∧ 0 < Criteria.quinticHurwitzDet2 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) ∧
      0 < Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
        (m.g.coeff0 m.Q) ∧
      0 < Criteria.quinticHurwitzDet4 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
        (m.g.coeff0 m.Q) := by
  obtain ⟨hN, hM, hD, hω⟩ := hp
  have hρ := ρ_pos (m := m) ⟨hN, hM, hD, hω⟩
  have hσ : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
  have h4 : 0 < m.g.coeff4 := by unfold coeff4; positivity
  have e0 := m.coeff0_eq hN.L.ne' hN.absSq_pos
  have hc : 0 < m.g.ωc * (m.g.ρ / m.g.M) := by positivity
  have e0' : m.g.coeff0 m.Q = m.g.ωc * (m.g.ρ / m.g.M) * m.K := by rw [e0]; ring
  unfold Model.Routh Criteria.QuinticRouth Criteria.quinticHurwitzDet5
  rw [e0']
  constructor
  · rintro ⟨-, h2, h3, h4', h5⟩
    refine ⟨?_, h2, h3, h4'⟩
    have : 0 < m.g.ωc * (m.g.ρ / m.g.M) * m.K := pos_of_mul_pos_left h5 h4'.le
    exact pos_of_mul_pos_right this hc.le
  · rintro ⟨hK, h2, h3, h4'⟩
    exact ⟨h4, h2, h3, h4', mul_pos (mul_pos hc hK) h4'⟩

/-- **Exact quintic boundary**: a balanced model with physical parameters is locally
exponentially stable iff `K > 0` and the Hurwitz determinants `Δ₂, Δ₃, Δ₄` of the monic
characteristic polynomial at the operating point are positive (`Δ₁ = 2σ + D/M + ω_c > 0`
always; `Δ₅ = a₀ Δ₄` with `a₀ = ω_c ρ K/M`; exactness
`VSMLPF.exactUnder_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      0 < m.K ∧ 0 < Criteria.quinticHurwitzDet2 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) ∧
        0 < Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
          (m.g.coeff0 m.Q) ∧
        0 < Criteria.quinticHurwitzDet4 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
          (m.g.coeff0 m.Q)) := by
  have hex := exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hex ⊢
  rw [← routh_iff hp]
  constructor
  · intro hs
    have hm := (Spectral.exactUnder_iff_forall.mp hex m
      ((TMIO.mem_realize _ _ _).mpr fun q hq => by
        rw [Set.mem_singleton_iff.mp hq]; exact hp)).mpr hs
    exact (TMIO.mem_realize _ _ _).mp hm .routh (by simp [family, translate, Spectral.table])
  · exact mem_den_locallyExponentiallyStable m hp hb

/-- **No reverse disagreement on the saddle side**: a negative synchronizing coefficient makes
the constant coefficient `ω_c ρ K/M` negative, so a balanced physical model with `K < 0` is
unstable (as is its quasi-static reduction). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_K_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m hp hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  rw [m.coeff0_eq hp.1.L.ne' hp.1.absSq_pos]
  exact mul_neg_of_pos_of_neg hp.2.2.2
    (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (ρ_pos hp) hK) hp.2.1)

/-! ## The phasor model stable, the full model unstable -/

/-- The quasi-static reduction of a model: the lossy three-state model `GFM.VSMLPFLossy` of the
same data about the same angle (`VSMLPF.reducedField_eq_lossy`). -/
def Model.toLossy (m : Model) : powerlib.GFM.VSMLPFLossy.Model := ⟨m.g.toLossy, m.δ⟩

/-- The quasi-static reduction is locally exponentially stable when the angle is balanced, the
parameters physical and `0 < K < D ω_c + D²/M` (the lossless reading,
`GFM.VSMLPFLossy.den_eq_preimage`, and `GFM.VSMLPF.mem_den_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] private theorem toLossy_mem_den_locallyExponentiallyStable
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hK : 0 < m.K)
    (hf : m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    m.toLossy ∈ powerlib.GFM.VSMLPFLossy.family.den (.flow .locallyExponentiallyStable) := by
  have hden := powerlib.GFM.VSMLPFLossy.den_eq_preimage
  unfold powerlib.TMIO.Statement at hden
  rw [hden, Set.mem_preimage]
  have hv := powerlib.GFM.VSMLPF.mem_den_locallyExponentiallyStable m.toLossy.toVSMLPF hp.2.1
    hp.2.2.1 hp.2.2.2 ?_ hK hf
  · unfold powerlib.TMIO.Statement at hv
    exact hv
  · change m.g.A * Real.sin (m.δ - m.g.α) = m.g.Pref - m.g.c0
    have hP := m.g.qssPower_eq_polar hp.1.absSq_pos m.δ
    have hb' : m.g.qssPower m.δ = m.g.Pref := hb
    linarith

/-- **Phasor model stable, full model unstable**: a balanced model with physical parameters whose
quasi-static reduction meets `0 < K < D ω_c + D²/M` and whose quintic Routh conditions are
strictly violated has a locally exponentially stable reduction (the lossy three-state model
`GFM.VSMLPFLossy`, `VSMLPF.Model.toLossy`) and is itself unstable. -/
@[tmio TM, powerlib_domain] theorem lossy_stable_full_unstable_of_violation (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : 0 < m.K)
    (hf : m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) (hv : m.RouthViolation) :
    connection% (m.toLossy ∈
        powerlib.GFM.VSMLPFLossy.family.den (.flow .locallyExponentiallyStable) ∧
      m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  exact ⟨toLossy_mem_den_locallyExponentiallyStable m hp hb hK hf, mem_den_unstable m hp hb hv⟩

/-- The lossy line `E = V = R = L = ω₀ = 1` (`X = 1`, `|Z|² = 2`) with `M = 1`, damping `D`,
filter bandwidth `ω_c` and zero set-point, read at `δ* = 0`: the zero-load point, current
`i_s(0) = 0`, `Q = 0`, `K = κ = 1/2`, `σ = 1`, `ρ = 2`. -/
def lossyWitness (D ωc : ℝ) : Model := ⟨⟨⟨⟨1, 1, 1, 1, 1⟩, 1, D, 0⟩, ωc⟩, 0⟩

/-- The witness below the boundary, `D = 1/2`, `ω_c = 1`. -/
def lowDamping : Model := lossyWitness (1 / 2) 1

/-- The witness above the boundary, `D = 1`, `ω_c = 1`. -/
def highDamping : Model := lossyWitness 1 1

@[tmio M, powerlib_domain] private theorem lossyWitness_physical {D ωc : ℝ} (hD : 0 < D)
    (hω : 0 < ωc) : Meets (lossyWitness D ωc) .physical :=
  ⟨⟨by norm_num [lossyWitness], by norm_num [lossyWitness], by norm_num [lossyWitness],
    by norm_num [lossyWitness], by norm_num [lossyWitness]⟩, by norm_num [lossyWitness], hD, hω⟩

@[tmio M, powerlib_domain] private theorem lossyWitness_is (D ωc : ℝ) :
    (lossyWitness D ωc).g.is 0 = 0 := by
  simp [Network.is, lossyWitness]

@[tmio M, powerlib_domain] private theorem lossyWitness_balanced (D ωc : ℝ) :
    Meets (lossyWitness D ωc) .balanced := by
  change (lossyWitness D ωc).g.qssPower 0 = 0
  simp [Network.qssPower, lossyWitness_is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem lossyWitness_Q (D ωc : ℝ) :
    (lossyWitness D ωc).Q = 0 := by
  change (lossyWitness D ωc).g.qssReactive 0 = 0
  simp [Network.qssReactive, lossyWitness_is, Network.reactive_eq]

@[tmio M, powerlib_domain] private theorem lossyWitness_K (D ωc : ℝ) :
    (lossyWitness D ωc).K = 1 / 2 := by
  have hZ : 0 < (lossyWitness D ωc).g.absSq := by
    norm_num [Network.absSq, Network.X, lossyWitness]
  have h := (lossyWitness D ωc).g.syncCoeff_add_qssReactive hZ 0
  have hQ : (lossyWitness D ωc).g.qssReactive 0 = 0 := lossyWitness_Q D ωc
  change (lossyWitness D ωc).g.syncCoeff 0 = 1 / 2
  rw [hQ, add_zero] at h
  rw [h]; norm_num [Network.κ, Network.absSq, Network.X, lossyWitness]

/-- **Boundary witness below the boundary**: at `D = 1/2`, `ω_c = 1` the quasi-static reduction
(`K = 1/2 < D ω_c + D²/M = 3/4`) is locally exponentially stable while the full model is unstable
(`Δ₄ = −233/8`). -/
@[tmio TM, powerlib_domain] theorem lowDamping_lossy_stable_full_unstable :
    connection% (lowDamping.toLossy ∈
        powerlib.GFM.VSMLPFLossy.family.den (.flow .locallyExponentiallyStable) ∧
      lowDamping ∈ family.den (.flow .unstable)) := by
  have hK : lowDamping.K = 1 / 2 := lossyWitness_K _ _
  refine lossy_stable_full_unstable_of_violation lowDamping
    (lossyWitness_physical (by norm_num) (by norm_num)) (lossyWitness_balanced _ _)
    (by rw [hK]; norm_num) (by rw [hK]; norm_num [lowDamping, lossyWitness]) ?_
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
  rw [lowDamping, lossyWitness_Q]
  norm_num [coeff4, coeff3, coeff2, coeff1, coeff0, VSM.coeff1, VSM.coeff0,
    Criteria.quinticHurwitzDet4, Criteria.quinticHurwitzDet3, Criteria.quinticHurwitzDet2,
    Network.ρ, Network.σ, Network.X, lossyWitness]

/-- **Boundary witness above the boundary**: at `D = 1`, `ω_c = 1` the full model is locally
exponentially stable (`Δ₁, …, Δ₅ = 4, 22, 104, 61, 61`). -/
@[tmio TM, powerlib_domain] theorem highDamping_stable :
    connection% (highDamping ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  refine mem_den_locallyExponentiallyStable highDamping
    (lossyWitness_physical (by norm_num) (by norm_num)) (lossyWitness_balanced 1 1) ?_
  rw [Model.Routh, highDamping, lossyWitness_Q]
  norm_num [coeff4, coeff3, coeff2, coeff1, coeff0, VSM.coeff1, VSM.coeff0, Criteria.QuinticRouth,
    Criteria.quinticHurwitzDet5, Criteria.quinticHurwitzDet4, Criteria.quinticHurwitzDet3,
    Criteria.quinticHurwitzDet2, Network.ρ, Network.σ, Network.X, lossyWitness]

end VSMLPF

/-! ## The power filter as a second time scale (reduced three-state model) -/

/-- **Filter limits**: for `p(s) = M det(sI − J)` of the three-state VSM + power filter at angle
`δ`, `K = K₀ cos δ`: `p(−ω_c) = ω_c K`, `p(−D/M) = ω_c K` and
`p(−(ω_c + D/M)) = ω_c (K − D ω_c − D²/M)`. -/
@[tmio M, powerlib_domain] theorem filter_charPoly_values (g : powerlib.GFM.VSMLPF)
    (hM : g.M ≠ 0) (δ : ℝ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ) (-(g.ωc : ℂ))).det =
        ((g.ωc * (g.K0 * Real.cos δ) : ℝ) : ℂ) ∧
      (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ) (-((g.D / g.M : ℝ) : ℂ))).det =
        ((g.ωc * (g.K0 * Real.cos δ) : ℝ) : ℂ) ∧
      (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ)
          (-((g.ωc + g.D / g.M : ℝ) : ℂ))).det =
        ((g.ωc * (g.K0 * Real.cos δ - g.D * g.ωc - g.D ^ 2 / g.M) : ℝ) : ℂ) := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  refine ⟨?_, ?_, ?_⟩ <;> rw [g.characteristic_polynomial hM] <;> push_cast <;> field_simp <;>
    ring

/-- **Real root of the reduced model on the stable side**: for `M, D, ω_c > 0`, `K > 0` and
`K < D ω_c + D²/M`, the characteristic polynomial of the three-state VSM + power filter has a
real root `λ ∈ (−(ω_c + D/M), −max(ω_c, D/M))`, and the complementary quadratic
`s² + b s + c` has `0 < b < min(ω_c, D/M)` (the real-part sum `−b` of the slow pair lies in
`(−min(ω_c, D/M), 0)`). -/
@[tmio M, powerlib_domain] theorem filter_real_root (g : powerlib.GFM.VSMLPF) (hM : 0 < g.M)
    (hD : 0 < g.D) (hω : 0 < g.ωc) (δ : ℝ) (hK : 0 < g.K0 * Real.cos δ)
    (hs : g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M) :
    ∃ l : ℝ, l ∈ Ioo (-(g.ωc + g.D / g.M)) (-max g.ωc (g.D / g.M)) ∧
      ∃ b c : ℝ, 0 < b ∧ b < min g.ωc (g.D / g.M) ∧
        ∀ s : ℂ, (Linear.characteristicMatrix (g.jacobian δ) s).det =
          (s - l) * (s ^ 2 + (b : ℂ) * s + (c : ℂ)) := by
  set K := g.K0 * Real.cos δ with hKdef
  set a2 := g.D / g.M + g.ωc
  set a1 := g.D * g.ωc / g.M
  set a0 := g.ωc * K / g.M
  have hmonic : ∀ s : ℂ, (Linear.characteristicMatrix (g.jacobian δ) s).det =
      s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) := by
    intro s
    have h := g.characteristic_polynomial hM.ne' δ s
    have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    apply mul_left_cancel₀ hM'
    rw [h]; simp only [a2, a1, a0, hKdef]; push_cast; field_simp
  set f : ℝ → ℝ := fun x => x ^ 3 + a2 * x ^ 2 + a1 * x + a0 with hf
  have hDM : 0 < g.D / g.M := div_pos hD hM
  have hlo : f (-(g.ωc + g.D / g.M)) < 0 := by
    have e : f (-(g.ωc + g.D / g.M)) = g.ωc * (K - g.D * g.ωc - g.D ^ 2 / g.M) / g.M := by
      simp only [hf, a2, a1, a0]; field_simp; ring
    rw [e]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hω (by linarith)) hM
  have hhi : 0 < f (-max g.ωc (g.D / g.M)) := by
    have e1 : f (-g.ωc) = g.ωc * K / g.M := by simp only [hf, a2, a1, a0]; field_simp; ring
    have e2 : f (-(g.D / g.M)) = g.ωc * K / g.M := by
      simp only [hf, a2, a1, a0]; field_simp; ring
    rcases le_total g.ωc (g.D / g.M) with h | h
    · rw [max_eq_right h, e2]; positivity
    · rw [max_eq_left h, e1]; positivity
  have hab : -(g.ωc + g.D / g.M) ≤ -max g.ωc (g.D / g.M) := by
    rcases le_total g.ωc (g.D / g.M) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hcont : ContinuousOn f (Icc (-(g.ωc + g.D / g.M)) (-max g.ωc (g.D / g.M))) := by
    apply Continuous.continuousOn; simp only [hf]; fun_prop
  obtain ⟨l, hl, hfl⟩ := intermediate_value_Ioo hab hcont ⟨hlo, hhi⟩
  refine ⟨l, hl, a2 + l, a1 + l * a2 + l ^ 2, ?_, ?_, fun s => ?_⟩
  · have := hl.1; simp only [a2]; linarith
  · have := hl.2
    rcases le_total g.ωc (g.D / g.M) with h | h
    · rw [max_eq_right h] at this; rw [min_eq_left h]; simp only [a2]; linarith
    · rw [max_eq_left h] at this; rw [min_eq_right h]; simp only [a2]; linarith
  · rw [hmonic, Criteria.cubic_factor_of_root hfl s]


/-! ## The four-state boundary as the line becomes fast

The four-state VSM on the line (`Line.VSM.family`, `theorem/GridTiedConverter/GFM/Line/VSM.lean`)
on lines of time scale `ε = 1/ω₀` with fixed `R` and reactance `X` (`L = ε X`,
`VSM.Model.atScale`): the exact Routh boundary in the damping is `D_line (1 + O(ε²))`, while the
quasi-static (swing) reduction is stable for every positive damping. -/

namespace VSM
open Filter Topology Asymptotics

/-- The increment identity of
`P(t) = α t + e (b₀ + b₁ t + b₂ t²) + e² (g₀ + g₁ t + g₂ t² + g₃ t³)`. -/
@[tmio T, powerlib_foundation] private theorem sandwich_increment
    (α b0 b1 b2 g0 g1 g2 g3 e s t : ℝ) :
    (α * t + e * (b0 + b1 * t + b2 * t ^ 2) + e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3)) -
        (α * s + e * (b0 + b1 * s + b2 * s ^ 2) + e ^ 2 * (g0 + g1 * s + g2 * s ^ 2 + g3 * s ^ 3)) =
      (t - s) * (α + e * (b1 + b2 * (s + t)) + e ^ 2 * (g1 + g2 * (s + t) +
        g3 * (s ^ 2 + s * t + t ^ 2))) := by
  ring

/-- The increment factor is at least `α/2` on `[−1, ∞)` for small `e`. -/
@[tmio T, powerlib_foundation] private theorem sandwich_factor {α b1 b2 g1 g2 g3 e s t : ℝ}
    (hb2 : 0 < b2) (hg3 : 0 ≤ g3)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hA : e * (|b1| + |g1| + 2 * b2 + 2 * |g2|) ≤ α / 2)
    (hB : e * |g2| ≤ b2) (hs : -1 ≤ s) (ht : -1 ≤ t) :
    α / 2 ≤ α + e * (b1 + b2 * (s + t)) + e ^ 2 * (g1 + g2 * (s + t) +
      g3 * (s ^ 2 + s * t + t ^ 2)) := by
  have hq : 0 ≤ e ^ 2 * (g3 * (s ^ 2 + s * t + t ^ 2)) :=
    mul_nonneg (sq_nonneg e) (mul_nonneg hg3 (by nlinarith [sq_nonneg (s + t), sq_nonneg s]))
  have h1 : -(e * |b1|) ≤ e * b1 := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le b1) he; linarith
  have hee : e ^ 2 ≤ e := by nlinarith
  have h2 : -(e * |g1|) ≤ e ^ 2 * g1 := by
    have a := mul_le_mul_of_nonneg_left (neg_abs_le g1) (sq_nonneg e)
    have b := mul_le_mul_of_nonneg_right hee (abs_nonneg g1)
    linarith
  have h3 : -(2 * (e * b2)) - 2 * (e * |g2|) ≤ e * (b2 * (s + t)) + e ^ 2 * (g2 * (s + t)) := by
    have hge : |e ^ 2 * (g2 * (s + t))| = e * (e * |g2|) * |s + t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg e)]; ring
    have hlow := neg_abs_le (e ^ 2 * (g2 * (s + t)))
    rcases le_or_gt 0 (s + t) with hu | hu
    · rw [abs_of_nonneg hu] at hge
      have k1 : e * (e * |g2|) * (s + t) ≤ e * b2 * (s + t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB he) hu
      have k2 : 0 ≤ e * b2 := mul_nonneg he hb2.le
      have k3 : 0 ≤ e * |g2| := mul_nonneg he (abs_nonneg _)
      nlinarith
    · have hu2 : |s + t| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have k1 : e * (e * |g2|) * |s + t| ≤ e * |g2| * 2 := by
        have : e * (e * |g2|) ≤ e * |g2| := by
          have := mul_le_mul_of_nonneg_right hee (abs_nonneg g2); nlinarith
        exact (mul_le_mul_of_nonneg_left hu2 (by positivity)).trans' (by
          have := mul_le_mul_of_nonneg_right this (abs_nonneg (s + t)); linarith)
      have k2 : -(2 * (e * b2)) ≤ e * (b2 * (s + t)) := by
        have h := mul_nonneg (mul_nonneg he hb2.le) (show (0 : ℝ) ≤ s + t + 2 by linarith)
        linarith
      linarith
  have hsum : e * (|b1| + |g1| + 2 * b2 + 2 * |g2|) =
      e * |b1| + e * |g1| + 2 * (e * b2) + 2 * (e * |g2|) := by ring
  nlinarith

/-- Near `c e`, `c = −b₀/α`, the polynomial is `α s` up to `K₀ e²`. -/
@[tmio T, powerlib_foundation] private theorem sandwich_value {α b0 b1 b2 g0 g1 g2 g3 e s : ℝ}
    (hα : 0 < α) (he : 0 < e) (he1 : e ≤ 1) (hs : |s| ≤ e) :
    |(α * (-b0 / α * e + s) + e * (b0 + b1 * (-b0 / α * e + s) + b2 * (-b0 / α * e + s) ^ 2) +
        e ^ 2 * (g0 + g1 * (-b0 / α * e + s) + g2 * (-b0 / α * e + s) ^ 2 +
          g3 * (-b0 / α * e + s) ^ 3)) - α * s| ≤
      ((|b1| + |b2| * (|-b0 / α| + 1)) * (|-b0 / α| + 1) + (|g0| + |g1| * (|-b0 / α| + 1) +
        |g2| * (|-b0 / α| + 1) ^ 2 + |g3| * (|-b0 / α| + 1) ^ 3)) * e ^ 2 := by
  set c := -b0 / α with hc
  set T0 := |c| + 1 with hT0
  set t := c * e + s with ht
  have hαc : α * c = -b0 := by rw [hc]; field_simp
  have hid : α * t + e * (b0 + b1 * t + b2 * t ^ 2) +
      e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3) - α * s =
      e * (b1 * t + b2 * t ^ 2) + e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3) := by
    rw [ht]; linear_combination e * hαc
  rw [hid]
  have hT0p : 1 ≤ T0 := by rw [hT0]; linarith [abs_nonneg c]
  have htb : |t| ≤ T0 * e := by
    rw [ht]
    calc |c * e + s| ≤ |c * e| + |s| := abs_add_le _ _
      _ = |c| * e + |s| := by rw [abs_mul, abs_of_pos he]
      _ ≤ |c| * e + e := by linarith
      _ = T0 * e := by rw [hT0]; ring
  have htT : |t| ≤ T0 := htb.trans (by nlinarith)
  have hq1 : |b1 * t + b2 * t ^ 2| ≤ (|b1| + |b2| * T0) * T0 * e := by
    have k : |b2| * |t| * |t| ≤ |b2| * T0 * |t| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htT (abs_nonneg _)) (abs_nonneg _)
    have k2 : (|b1| + |b2| * T0) * |t| ≤ (|b1| + |b2| * T0) * (T0 * e) :=
      mul_le_mul_of_nonneg_left htb (by positivity)
    calc |b1 * t + b2 * t ^ 2| ≤ |b1 * t| + |b2 * t ^ 2| := abs_add_le _ _
      _ = |b1| * |t| + |b2| * |t| * |t| := by rw [abs_mul, abs_mul, abs_pow, sq]; ring
      _ ≤ (|b1| + |b2| * T0) * (T0 * e) := by nlinarith
      _ = (|b1| + |b2| * T0) * T0 * e := by ring
  have hq2 : |g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3| ≤
      |g0| + |g1| * T0 + |g2| * T0 ^ 2 + |g3| * T0 ^ 3 := by
    have a1 : |g1 * t| ≤ |g1| * T0 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left htT (abs_nonneg _)
    have a2 : |g2 * t ^ 2| ≤ |g2| * T0 ^ 2 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htT 2) (abs_nonneg _)
    have a3 : |g3 * t ^ 3| ≤ |g3| * T0 ^ 3 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htT 3) (abs_nonneg _)
    have b1' := abs_add_le (g0 + g1 * t + g2 * t ^ 2) (g3 * t ^ 3)
    have b2' := abs_add_le (g0 + g1 * t) (g2 * t ^ 2)
    have b3' := abs_add_le g0 (g1 * t)
    linarith
  have he2 : 0 < e ^ 2 := by positivity
  calc |e * (b1 * t + b2 * t ^ 2) + e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3)|
      ≤ |e * (b1 * t + b2 * t ^ 2)| + |e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3)| :=
        abs_add_le _ _
    _ = e * |b1 * t + b2 * t ^ 2| + e ^ 2 * |g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3| := by
        rw [abs_mul, abs_mul, abs_of_pos he, abs_of_pos he2]
    _ ≤ e * ((|b1| + |b2| * T0) * T0 * e) +
        e ^ 2 * (|g0| + |g1| * T0 + |g2| * T0 ^ 2 + |g3| * T0 ^ 3) := by
        gcongr
    _ = ((|b1| + |b2| * T0) * T0 + (|g0| + |g1| * T0 + |g2| * T0 ^ 2 + |g3| * T0 ^ 3)) *
        e ^ 2 := by ring

/-- A polynomial `α t + e (b₀ + b₁ t + b₂ t²) + e² (g₀ + g₁ t + g₂ t² + g₃ t³)` with `α, b₂ > 0`,
`g₃ ≥ 0` changes sign on `[−1, ∞)` within `C e²` of `c e`, `c = −b₀/α`: for one `C > 0` and every
small `e > 0` it is positive for `t ≥ c e + C e²` and negative for `−1 ≤ t ≤ c e − C e²`. -/
@[tmio T, powerlib_foundation] private theorem quadratic_sandwich {α b0 b1 b2 g0 g1 g2 g3 : ℝ}
    (hα : 0 < α) (hb2 : 0 < b2) (hg3 : 0 ≤ g3) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧ ∀ e : ℝ, 0 < e → e < e0 →
      (∀ t : ℝ, -b0 / α * e + C * e ^ 2 ≤ t → 0 < α * t + e * (b0 + b1 * t + b2 * t ^ 2) +
        e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3)) ∧
      (∀ t : ℝ, -1 ≤ t → t ≤ -b0 / α * e - C * e ^ 2 → α * t + e * (b0 + b1 * t + b2 * t ^ 2) +
        e ^ 2 * (g0 + g1 * t + g2 * t ^ 2 + g3 * t ^ 3) < 0) := by
  set c := -b0 / α with hc
  set K0 := (|b1| + |b2| * (|c| + 1)) * (|c| + 1) + (|g0| + |g1| * (|c| + 1) +
    |g2| * (|c| + 1) ^ 2 + |g3| * (|c| + 1) ^ 3) with hK0
  have hK0n : 0 ≤ K0 := by positivity
  set C := 2 * K0 / α + 1 with hCdef
  have hCpos : 0 < C := by positivity
  set B := |b1| + |g1| + 2 * b2 + 2 * |g2| + 1 with hB
  refine ⟨C, min 1 (min (α / (2 * B)) (min (b2 / (|g2| + 1)) (1 / (C + |c| + 1)))), hCpos,
    by positivity, fun e he he0 => ?_⟩
  have he1 : e < 1 := lt_of_lt_of_le he0 (min_le_left _ _)
  have heA : e < α / (2 * B) :=
    lt_of_lt_of_le he0 ((min_le_right _ _).trans (min_le_left _ _))
  have heB : e < b2 / (|g2| + 1) :=
    lt_of_lt_of_le he0 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heC : e < 1 / (C + |c| + 1) :=
    lt_of_lt_of_le he0 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hBpos : 0 < B := by positivity
  have kA : e * (|b1| + |g1| + 2 * b2 + 2 * |g2|) ≤ α / 2 := by
    have h := (lt_div_iff₀ (by positivity)).mp heA
    have h2 : e * (|b1| + |g1| + 2 * b2 + 2 * |g2|) ≤ e * B :=
      mul_le_mul_of_nonneg_left (by rw [hB]; linarith) he.le
    linarith
  have kB : e * |g2| ≤ b2 := by
    have h := (lt_div_iff₀ (by positivity)).mp heB
    have h2 : e * |g2| ≤ e * (|g2| + 1) := mul_le_mul_of_nonneg_left (by linarith) he.le
    linarith
  have kC : e * (C + |c| + 1) ≤ 1 := by
    have h := (lt_div_iff₀ (by positivity)).mp heC
    linarith
  have hCe1 : C * e ≤ 1 := by
    have h2 : e * C ≤ e * (C + |c| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg c]) he.le
    linarith
  have hCe : C * e ^ 2 ≤ e := by
    have h2 : C * e * e ≤ 1 * e := mul_le_mul_of_nonneg_right hCe1 he.le
    have : C * e ^ 2 = C * e * e := by ring
    linarith
  have hce : |c| * e + C * e ^ 2 ≤ 1 := by
    have h2 : C * e ^ 2 ≤ C * e := by
      have : e ^ 2 ≤ e := by nlinarith
      exact mul_le_mul_of_nonneg_left this hCpos.le
    have : e * (C + |c| + 1) = C * e + |c| * e + e := by ring
    linarith
  have hc1 : -(|c| * e) ≤ c * e := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le c) he.le
    linarith
  have hlow : -1 ≤ c * e - C * e ^ 2 := by linarith
  have hup : -1 ≤ c * e + C * e ^ 2 := by
    have : 0 ≤ C * e ^ 2 := by positivity
    linarith
  have hpos := sandwich_value (b0 := b0) (b1 := b1) (b2 := b2) (g0 := g0) (g1 := g1) (g2 := g2)
    (g3 := g3) hα he he1.le (s := C * e ^ 2) (by rw [abs_of_pos (by positivity)]; exact hCe)
  have hneg := sandwich_value (b0 := b0) (b1 := b1) (b2 := b2) (g0 := g0) (g1 := g1) (g2 := g2)
    (g3 := g3) hα he he1.le (s := -(C * e ^ 2))
    (by rw [abs_neg, abs_of_pos (by positivity)]; exact hCe)
  rw [← hc, ← hK0] at hpos hneg
  have hαC : α * (C * e ^ 2) = (2 * K0 + α) * e ^ 2 := by
    rw [hCdef]; field_simp
  have hKa : 0 < (K0 + α) * e ^ 2 := by positivity
  refine ⟨fun t ht => ?_, fun t ht1 ht2 => ?_⟩
  · have hinc := sandwich_increment α b0 b1 b2 g0 g1 g2 g3 e (c * e + C * e ^ 2) t
    have hf := sandwich_factor (g3 := g3) hb2 hg3 he.le he1.le kA kB hup (by linarith)
      (t := t)
    have hP0 := (abs_le.mp hpos).1
    have hm := mul_nonneg (sub_nonneg.mpr ht) (show (0 : ℝ) ≤ α + e * (b1 + b2 *
      (c * e + C * e ^ 2 + t)) + e ^ 2 * (g1 + g2 * (c * e + C * e ^ 2 + t) +
        g3 * ((c * e + C * e ^ 2) ^ 2 + (c * e + C * e ^ 2) * t + t ^ 2)) by linarith)
    linarith
  · have hinc := sandwich_increment α b0 b1 b2 g0 g1 g2 g3 e t (c * e - C * e ^ 2)
    have hf := sandwich_factor (g3 := g3) hb2 hg3 he.le he1.le kA kB ht1 hlow
    have hP0 := (abs_le.mp hneg).2
    rw [show c * e + -(C * e ^ 2) = c * e - C * e ^ 2 by ring] at hP0
    have hm := mul_nonneg (sub_nonneg.mpr ht2) (show (0 : ℝ) ≤ α + e * (b1 + b2 *
      (t + (c * e - C * e ^ 2))) + e ^ 2 * (g1 + g2 * (t + (c * e - C * e ^ 2)) +
        g3 * (t ^ 2 + t * (c * e - C * e ^ 2) + (c * e - C * e ^ 2) ^ 2)) by linarith)
    have hαC' : α * -(C * e ^ 2) = -((2 * K0 + α) * e ^ 2) := by linarith
    linarith

/-- The model `m` with damping `D` on a line of time scale `ε = 1/ω₀`: nominal frequency `1/ε`
and inductance `ε X`, `X = ω₀ L` the reactance of `m` (so the reactance, the quasi-static power
curve and `K`, `Q`, `κ` stay those of `m`; `σ = (R/X)/ε`, `ρ = (1 + (R/X)²)/ε²`). -/
def Model.atScale (m : Model) (ε D : ℝ) : Model :=
  ⟨⟨⟨m.g.E, m.g.V, m.g.R, ε * m.g.X, 1 / ε⟩, m.g.M, D, m.g.Pref⟩, m.δ⟩

/-- The line damping at scale `ε`, `D_line = 2 E² R X L/|Z|⁴` with `L = ε X`
(`VSM.Model.atScale_Dline`). -/
def Model.DlineAt (m : Model) (ε : ℝ) : ℝ :=
  ε * (2 * m.g.E ^ 2 * m.g.R * m.g.X ^ 2 / m.g.absSq ^ 2)

section
variable (m : Model) {ε : ℝ} (D : ℝ)

@[tmio M, powerlib_domain] private theorem atScale_X (hε : ε ≠ 0) :
    (m.atScale ε D).g.X = m.g.X := by
  simp only [Model.atScale, Network.X]
  field_simp

@[tmio M, powerlib_domain] private theorem atScale_absSq (hε : ε ≠ 0) :
    (m.atScale ε D).g.absSq = m.g.absSq := by
  rw [Network.absSq, atScale_X m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_σ :
    (m.atScale ε D).g.σ = m.g.R / m.g.X / ε := by
  simp only [Network.σ, Model.atScale]; ring

@[tmio M, powerlib_domain] private theorem atScale_ρ (hε : ε ≠ 0) (hX : m.g.X ≠ 0) :
    (m.atScale ε D).g.ρ = (1 + (m.g.R / m.g.X) ^ 2) / ε ^ 2 := by
  rw [Network.ρ, atScale_σ m D, atScale_X m D hε]
  simp only [Model.atScale]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem atScale_κ (hε : ε ≠ 0) :
    (m.atScale ε D).g.κ = m.g.κ := by
  rw [Network.κ, atScale_X m D hε, atScale_absSq m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_A (hε : ε ≠ 0) :
    (m.atScale ε D).g.A = m.g.A := by
  rw [Network.A, atScale_absSq m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_α (hε : ε ≠ 0) :
    (m.atScale ε D).g.α = m.g.α := by
  rw [Network.α, atScale_X m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_c0 (hε : ε ≠ 0) :
    (m.atScale ε D).g.c0 = m.g.c0 := by
  rw [Network.c0, atScale_absSq m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_K (hε : ε ≠ 0) :
    (m.atScale ε D).K = m.K := by
  rw [Model.K, Model.K, Network.syncCoeff, Network.syncCoeff, atScale_A m D hε,
    atScale_α m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_Q (hε : ε ≠ 0) (hZ : 0 < m.g.absSq) :
    (m.atScale ε D).Q = m.Q := by
  have hZ' : 0 < (m.atScale ε D).g.absSq := by rwa [atScale_absSq m D hε]
  rw [Model.Q, Model.Q, Network.qssReactive_eq_polar _ hZ', Network.qssReactive_eq_polar _ hZ,
    atScale_κ m D hε, atScale_A m D hε, atScale_α m D hε]; rfl

@[tmio M, powerlib_domain] private theorem atScale_qssPower (hε : ε ≠ 0) (hZ : 0 < m.g.absSq) :
    (m.atScale ε D).g.qssPower (m.atScale ε D).δ = m.g.qssPower m.δ := by
  have hZ' : 0 < (m.atScale ε D).g.absSq := by rwa [atScale_absSq m D hε]
  rw [Network.qssPower_eq_polar _ hZ', Network.qssPower_eq_polar _ hZ, atScale_c0 m D hε,
    atScale_A m D hε, atScale_α m D hε]; rfl

/-- The line damping of the scaled model is `D_line(ε) = ε · 2 E² R X²/|Z|⁴`. -/
@[tmio M, powerlib_domain] theorem Model.atScale_Dline (hε : ε ≠ 0) :
    (m.atScale ε D).g.Dline = m.DlineAt ε := by
  rw [Network.Dline, atScale_X m D hε, atScale_absSq m D hε, Model.DlineAt]
  simp only [Model.atScale]
  ring

end

/-- The third Hurwitz determinant of the four-state quartic on a line of time scale `ε`
(`σ = r/ε`, `ρ = (1 + r²)/ε²`, `Q = κ − K`) at the damping `D = ε D̂ (1 + t)`,
`D̂ = 2 r κ/(1 + r²)`, as a polynomial in `t` and `ε²`. -/
@[tmio T, powerlib_foundation] private theorem hurwitzDet_scaled_eq {M K κ r ε t : ℝ} (hM : M ≠ 0)
    (hε : ε ≠ 0) :
    (2 * (r / ε) + ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) / M) *
        ((1 + r ^ 2) / ε ^ 2 + (2 * (r / ε) * (ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t)) -
          (κ - K)) / M) *
        ((ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) * ((1 + r ^ 2) / ε ^ 2) -
          2 * (r / ε) * (κ - K)) / M) -
      (((ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) * ((1 + r ^ 2) / ε ^ 2) -
          2 * (r / ε) * (κ - K)) / M) ^ 2 +
        (2 * (r / ε) + ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) / M) ^ 2 *
          ((1 + r ^ 2) / ε ^ 2 * K / M)) =
      4 * κ * r ^ 2 / ((1 + r ^ 2) ^ 2 * M ^ 3 * ε ^ 4) *
        (M ^ 2 * (1 + r ^ 2) ^ 3 * t +
          ε ^ 2 * (2 * K * M * (1 + r ^ 2) * (r ^ 2 - 1) +
            2 * M * (1 + r ^ 2) * (K * (r ^ 2 - 1) + 2 * κ * r ^ 2) * t +
            4 * M * κ * r ^ 2 * (1 + r ^ 2) * t ^ 2) +
          ε ^ 4 * (K * (K * (1 + r ^ 2) + 2 * κ * (r ^ 2 - 1)) +
            (K ^ 2 * (1 + r ^ 2) + 6 * K * κ * r ^ 2 - 2 * K * κ + 3 * κ ^ 2 * r ^ 2 - κ ^ 2) * t +
            κ * (4 * K * r ^ 2 + 7 * κ * r ^ 2 - κ) * t ^ 2 + 4 * κ ^ 2 * r ^ 2 * t ^ 3)) := by
  have hN : (1 + r ^ 2) ≠ 0 := by positivity
  field_simp
  ring


/-- The second-order coefficient of the critical damping on fast lines,
`c₂ = 2 (K/M)(1 − r²)/(1 + r²)²`, `r = R/X` (`VSM.Model.isBigO_Dcrit_sub`). -/
def Model.DcritCoeff (m : Model) : ℝ :=
  2 * (m.K / m.g.M) * (1 - (m.g.R / m.g.X) ^ 2) / (1 + (m.g.R / m.g.X) ^ 2) ^ 2

/-- The shift `c ε² + C ε⁴` keeps `κ t + K` and `1 + t` positive on small scales. -/
@[tmio T, powerlib_foundation] private theorem small_shift {c κ K ε C t : ℝ} (hκ : 0 < κ)
    (hK : 0 < K) (hε : 0 < ε) (hε1 : ε < 1) (hεK : ε * ((|c| + 1) * (κ + K)) < K) (hC : 0 ≤ C)
    (ht : c * ε ^ 2 + C * ε ^ 4 ≤ t) : 0 < κ * t + K ∧ 0 < 1 + t := by
  have he2 : ε ^ 2 ≤ ε := pow_le_of_le_one hε.le hε1.le (by norm_num)
  obtain ⟨y, hydef⟩ : ∃ y, y = |c| * ε ^ 2 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hydef]; positivity
  have hyε : y ≤ |c| * ε := by rw [hydef]; exact mul_le_mul_of_nonneg_left he2 (abs_nonneg c)
  have hy : y * (κ + K) < K := by
    have h1 : y * (κ + K) ≤ |c| * ε * (κ + K) :=
      mul_le_mul_of_nonneg_right hyε (by positivity)
    have h2 : |c| * ε * (κ + K) ≤ ε * ((|c| + 1) * (κ + K)) := by
      have e : |c| * ε * (κ + K) = ε * (|c| * (κ + K)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hε.le
    linarith
  have htc : -y ≤ t := by
    have h1 : -|c| * ε ^ 2 ≤ c * ε ^ 2 := mul_le_mul_of_nonneg_right (neg_abs_le c) (sq_nonneg ε)
    have h2 : 0 ≤ C * ε ^ 4 := by positivity
    rw [hydef]
    linarith
  have hKy : 0 ≤ K * y := mul_nonneg hK.le hy0
  have hκy : 0 ≤ κ * y := mul_nonneg hκ.le hy0
  have hexp : y * (κ + K) = κ * y + K * y := by ring
  constructor
  · have h1 : κ * -y ≤ κ * t := mul_le_mul_of_nonneg_left htc hκ.le
    linarith
  · have hy1 : y < 1 := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_left h hK.le
      linarith
    linarith

/-- **Routh boundary at `D_line(1 + c₂ ε² + O(ε⁴))`, static form.** For `E ≠ 0`, `R, X, M > 0`
and `K > 0` there are `C > 0` and `ε₀ > 0` such that on every line of time scale `ε ∈ (0, ε₀)` a
positive damping `D ≥ D_line(ε)(1 + c₂ ε² + C ε⁴)` meets the quartic Routh conditions and a
positive damping `D ≤ D_line(ε)(1 + c₂ ε² − C ε⁴)` strictly violates them,
`c₂ = Model.DcritCoeff = 2 (K/M)(1 − r²)/(1 + r²)²`. The determinant at
`D = D_line(ε)(1 + t)` is `ε⁻⁴` times a polynomial `α t + ε² (b₀ + …) + ε⁴ (…)`, `α > 0`,
`c₂ = −b₀/α`. -/
@[tmio M, powerlib_domain] theorem Model.exists_routh_sandwich_two (m : Model) (hE : m.g.E ≠ 0)
    (hR : 0 < m.g.R) (hX : 0 < m.g.X) (hM : 0 < m.g.M) (hK : 0 < m.K) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ D : ℝ, 0 < D →
      (m.DlineAt ε * (1 + m.DcritCoeff * ε ^ 2 + C * ε ^ 4) ≤ D → (m.atScale ε D).Routh) ∧
      (D ≤ m.DlineAt ε * (1 + m.DcritCoeff * ε ^ 2 - C * ε ^ 4) →
        (m.atScale ε D).RouthViolation) := by
  have hZ : 0 < m.g.absSq := by unfold Network.absSq; positivity
  obtain ⟨r, hr⟩ : ∃ r, r = m.g.R / m.g.X := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = m.g.κ := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = m.K := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = m.g.M := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ div_pos hR hX
  have hκ : 0 < κ := by
    rw [hκdef, Network.κ]; have := pow_pos (abs_pos.mpr hE) 2; rw [sq_abs] at this; positivity
  rw [← hKdef] at hK
  rw [← hMdef] at hM
  have hQ : m.Q = κ - K := by
    have := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [hκdef, hKdef, Model.Q, Model.K]; linarith
  obtain ⟨C, e0, hC, he0, H⟩ := quadratic_sandwich (α := M ^ 2 * (1 + r ^ 2) ^ 3)
    (b0 := 2 * K * M * (1 + r ^ 2) * (r ^ 2 - 1))
    (b1 := 2 * M * (1 + r ^ 2) * (K * (r ^ 2 - 1) + 2 * κ * r ^ 2))
    (b2 := 4 * M * κ * r ^ 2 * (1 + r ^ 2)) (g0 := K * (K * (1 + r ^ 2) + 2 * κ * (r ^ 2 - 1)))
    (g1 := K ^ 2 * (1 + r ^ 2) + 6 * K * κ * r ^ 2 - 2 * K * κ + 3 * κ ^ 2 * r ^ 2 - κ ^ 2)
    (g2 := κ * (4 * K * r ^ 2 + 7 * κ * r ^ 2 - κ)) (g3 := 4 * κ ^ 2 * r ^ 2)
    (by positivity) (by positivity) (by positivity)
  set c := m.DcritCoeff with hcdef
  have hc2 : -(2 * K * M * (1 + r ^ 2) * (r ^ 2 - 1)) / (M ^ 2 * (1 + r ^ 2) ^ 3) = c := by
    rw [hcdef, Model.DcritCoeff, ← hr, ← hKdef, ← hMdef]
    field_simp
    ring
  rw [hc2] at H
  refine ⟨C, hC, min 1 (min e0 (K / ((|c| + 1) * (κ + K)))), by positivity,
    fun ε hε hεε0 D hD => ?_⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεε0 (min_le_left _ _)
  have hεe : ε < e0 := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_left _ _))
  have hεK : ε < K / ((|c| + 1) * (κ + K)) :=
    lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_right _ _))
  have he2 : ε ^ 2 ≤ ε := pow_le_of_le_one hε.le hε1.le (by norm_num)
  obtain ⟨Hup, Hdn⟩ := H (ε ^ 2) (by positivity) (lt_of_le_of_lt he2 hεe)
  have h4 : (ε ^ 2) ^ 2 = ε ^ 4 := by ring
  rw [h4] at Hup Hdn
  have hdl0 : 0 < ε * (2 * r * κ / (1 + r ^ 2)) := by positivity
  have hDl : m.DlineAt ε = ε * (2 * r * κ / (1 + r ^ 2)) := by
    rw [Model.DlineAt, hr, hκdef, Network.κ]
    unfold Network.absSq at hZ ⊢
    field_simp
    ring
  obtain ⟨t, ht⟩ : ∃ t, t = D / (ε * (2 * r * κ / (1 + r ^ 2))) - 1 := ⟨_, rfl⟩
  have hDt : D = ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) := by
    rw [ht]; field_simp; ring
  have hε' := hε.ne'
  have hQ' : (m.atScale ε D).Q = κ - K := by rw [atScale_Q m D hε' hZ, hQ]
  have hσ : (m.atScale ε D).g.σ = r / ε := by rw [atScale_σ, hr]
  have hρ : (m.atScale ε D).g.ρ = (1 + r ^ 2) / ε ^ 2 := by rw [atScale_ρ m D hε' hX.ne', hr]
  have e3 : (m.atScale ε D).g.coeff3 =
      2 * (r / ε) + ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) / M := by
    rw [coeff3, hσ, hMdef, ← hDt]; rfl
  have e2 : (m.atScale ε D).g.coeff2 (m.atScale ε D).Q =
      (1 + r ^ 2) / ε ^ 2 + (2 * (r / ε) * (ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t)) -
        (κ - K)) / M := by
    rw [coeff2, hσ, hρ, hQ', hMdef, ← hDt]; rfl
  have e1 : (m.atScale ε D).g.coeff1 (m.atScale ε D).Q =
      (ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) * ((1 + r ^ 2) / ε ^ 2) -
        2 * (r / ε) * (κ - K)) / M := by
    rw [coeff1, hσ, hρ, hQ', hMdef, ← hDt]; rfl
  have e0 : (m.atScale ε D).g.coeff0 (m.atScale ε D).Q = (1 + r ^ 2) / ε ^ 2 * K / M := by
    have hL : (m.atScale ε D).g.L ≠ 0 := mul_ne_zero hε' hX.ne'
    have hZ' : 0 < (m.atScale ε D).g.absSq := by rwa [atScale_absSq m D hε']
    rw [Model.coeff0_eq _ hL hZ', hρ, atScale_K m D hε', ← hKdef, hMdef]; rfl
  have hid := hurwitzDet_scaled_eq (M := M) (K := K) (κ := κ) (r := r) (t := t) hM.ne' hε'
  have hF : 0 < 4 * κ * r ^ 2 / ((1 + r ^ 2) ^ 2 * M ^ 3 * ε ^ 4) := by positivity
  constructor
  · intro hup
    have htC : c * ε ^ 2 + C * ε ^ 4 ≤ t := by
      rw [hDl] at hup
      rw [ht, le_sub_iff_add_le, le_div_iff₀ hdl0]; linarith
    have hP := Hup t htC
    obtain ⟨hKt, ht1⟩ := small_shift hκ hK hε hε1 ((lt_div_iff₀ (by positivity)).mp hεK)
      hC.le htC
    unfold Model.Routh
    rw [e3, e2, e1, e0]
    refine ⟨by positivity, ?_, by positivity, ?_⟩
    · apply div_pos _ hM
      have : ε * (2 * r * κ / (1 + r ^ 2)) * (1 + t) * ((1 + r ^ 2) / ε ^ 2) -
          2 * (r / ε) * (κ - K) = 2 * r / ε * (κ * t + K) := by
        field_simp; ring
      rw [this]; positivity
    · linarith [mul_pos hF hP, hid]
  · intro hdn
    have htC : t ≤ c * ε ^ 2 - C * ε ^ 4 := by
      rw [hDl] at hdn
      rw [ht, sub_le_iff_le_add, div_le_iff₀ hdl0]; linarith
    have ht1 : -1 ≤ t := by
      have : 0 < D / (ε * (2 * r * κ / (1 + r ^ 2))) := div_pos hD hdl0
      rw [ht]; linarith
    have hP := Hdn t ht1 htC
    unfold Model.RouthViolation
    rw [e3, e2, e1, e0]
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    linarith [mul_neg_of_pos_of_neg hF hP, hid]

/-- **Routh boundary at `D_line(1 + O(ε²))`, static form.** For `E ≠ 0`, `R, X, M > 0` and
`K > 0` there are `C > 0` and `ε₀ > 0` such that on every line of time scale `ε ∈ (0, ε₀)` a
positive damping `D ≥ D_line(ε)(1 + C ε²)` meets the quartic Routh conditions and a positive
damping `D ≤ D_line(ε)(1 − C ε²)` strictly violates them (the first-order form of
`VSM.Model.exists_routh_sandwich_two`). -/
@[tmio M, powerlib_domain] theorem Model.exists_routh_sandwich (m : Model) (hE : m.g.E ≠ 0)
    (hR : 0 < m.g.R) (hX : 0 < m.g.X) (hM : 0 < m.g.M) (hK : 0 < m.K) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ D : ℝ, 0 < D →
      (m.DlineAt ε * (1 + C * ε ^ 2) ≤ D → (m.atScale ε D).Routh) ∧
      (D ≤ m.DlineAt ε * (1 - C * ε ^ 2) → (m.atScale ε D).RouthViolation) := by
  obtain ⟨C, hC, ε0, hε0, H⟩ := m.exists_routh_sandwich_two hE hR hX hM hK
  refine ⟨|m.DcritCoeff| + C, by positivity, min ε0 1, by positivity,
    fun ε hε hεε0 D hD => ?_⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεε0 (min_le_right _ _)
  obtain ⟨Hup, Hdn⟩ := H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _)) D hD
  have hZ : 0 < m.g.absSq := by unfold Network.absSq; positivity
  have hDl : 0 ≤ m.DlineAt ε := by
    have := pow_pos (abs_pos.mpr hE) 2; rw [sq_abs] at this
    unfold Model.DlineAt; positivity
  have h4 : C * ε ^ 4 ≤ C * ε ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hε.le hε1.le (by norm_num)) hC.le
  have hc1 : m.DcritCoeff * ε ^ 2 ≤ |m.DcritCoeff| * ε ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg ε)
  have hc2 : -(|m.DcritCoeff| * ε ^ 2) ≤ m.DcritCoeff * ε ^ 2 := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le m.DcritCoeff) (sq_nonneg ε); linarith
  constructor
  · intro h
    refine Hup (le_trans (mul_le_mul_of_nonneg_left ?_ hDl) h)
    linarith
  · intro h
    refine Hdn (le_trans h (mul_le_mul_of_nonneg_left ?_ hDl))
    linarith

/-- The critical damping at scale `ε`: the infimum of the positive dampings whose model meets
the quartic Routh conditions (by `VSM.mem_den_locallyExponentiallyStable_iff` the boundary of
local exponential stability of a balanced physical model). -/
def Model.Dcrit (m : Model) (ε : ℝ) : ℝ := sInf {D : ℝ | 0 < D ∧ (m.atScale ε D).Routh}

/-- **`D_crit = D_line (1 + c₂ ε² + O(ε⁴))` as `ε = 1/ω₀ → 0⁺`** (`R, X` fixed, `L = ε X`): for
`E ≠ 0`, `R, X, M > 0` and `K > 0`,
`D_crit(ε)/D_line(ε) − 1 − c₂ ε² = O(ε⁴)` with the second-order coefficient
`c₂ = 2 (K/M)(1 − r²)/(1 + r²)²`, `r = R/X` (`VSM.Model.DcritCoeff`;
`VSM.Model.exists_routh_sandwich_two`). In particular the full model needs more damping than
`D_line` on a fast line with `R < X` and less with `R > X`. -/
@[tmio M, powerlib_domain] theorem Model.isBigO_Dcrit_sub (m : Model) (hE : m.g.E ≠ 0)
    (hR : 0 < m.g.R) (hX : 0 < m.g.X) (hM : 0 < m.g.M) (hK : 0 < m.K) :
    (fun ε => m.Dcrit ε / m.DlineAt ε - 1 - m.DcritCoeff * ε ^ 2) =O[𝓝[>] 0]
      (fun ε => ε ^ 4) := by
  obtain ⟨C, hC, ε0, hε0, H⟩ := m.exists_routh_sandwich_two hE hR hX hM hK
  set c := m.DcritCoeff with hc
  refine IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT (show 0 < min ε0 (min 1 (1 / (|c| + C + 1))) by positivity)]
    with ε ⟨hε, hεε0⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε < 1 / (|c| + C + 1) :=
    lt_of_lt_of_le hεε0 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Hs⟩ : Nonempty (∀ D : ℝ, 0 < D →
      (m.DlineAt ε * (1 + c * ε ^ 2 + C * ε ^ 4) ≤ D → (m.atScale ε D).Routh) ∧
      (D ≤ m.DlineAt ε * (1 + c * ε ^ 2 - C * ε ^ 4) → (m.atScale ε D).RouthViolation)) :=
    ⟨H ε hε (lt_of_lt_of_le hεε0 (min_le_left _ _))⟩
  have hZ : 0 < m.g.absSq := by unfold Network.absSq; positivity
  have hDl : 0 < m.DlineAt ε := by
    have := pow_pos (abs_pos.mpr hE) 2; rw [sq_abs] at this
    unfold Model.DlineAt; positivity
  have hsmall : |c| * ε ^ 2 + C * ε ^ 4 < 1 := by
    have h := (lt_div_iff₀ (by positivity)).mp hεc
    have e2 : ε ^ 2 ≤ ε := pow_le_of_le_one hε.le hε1.le (by norm_num)
    have e4 : ε ^ 4 ≤ ε := pow_le_of_le_one hε.le hε1.le (by norm_num)
    have : |c| * ε ^ 2 ≤ |c| * ε := mul_le_mul_of_nonneg_left e2 (abs_nonneg c)
    have : C * ε ^ 4 ≤ C * ε := mul_le_mul_of_nonneg_left e4 hC.le
    linarith
  have hc1 : -(|c| * ε ^ 2) ≤ c * ε ^ 2 := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le c) (sq_nonneg ε); linarith
  have hpos : 0 < m.DlineAt ε * (1 + c * ε ^ 2 + C * ε ^ 4) := by
    apply mul_pos hDl
    have : 0 ≤ C * ε ^ 4 := by positivity
    linarith
  have hup : m.DlineAt ε * (1 + c * ε ^ 2 + C * ε ^ 4) ∈
      {D : ℝ | 0 < D ∧ (m.atScale ε D).Routh} :=
    ⟨hpos, (Hs _ hpos).1 le_rfl⟩
  have hlow : ∀ D ∈ {D : ℝ | 0 < D ∧ (m.atScale ε D).Routh},
      m.DlineAt ε * (1 + c * ε ^ 2 - C * ε ^ 4) ≤ D := by
    rintro D ⟨hD, hr⟩
    by_contra h
    push Not at h
    have hv := (Hs D hD).2 h.le
    obtain ⟨h3, h1, h0, hg⟩ := hr
    have h2 := Criteria.quartic_routh_a2_pos h3 h1 h0 hg
    rcases hv with v | v | v | v | v <;> linarith
  have h1 : m.Dcrit ε ≤ m.DlineAt ε * (1 + c * ε ^ 2 + C * ε ^ 4) :=
    csInf_le ⟨0, fun D hD => hD.1.le⟩ hup
  have h2 : m.DlineAt ε * (1 + c * ε ^ 2 - C * ε ^ 4) ≤ m.Dcrit ε := le_csInf ⟨_, hup⟩ hlow
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 4),
    abs_le]
  constructor
  · have : m.DlineAt ε * (1 + c * ε ^ 2 - C * ε ^ 4) / m.DlineAt ε ≤ m.Dcrit ε / m.DlineAt ε :=
      div_le_div_of_nonneg_right h2 hDl.le
    rw [mul_div_cancel_left₀ _ hDl.ne'] at this
    linarith
  · have : m.Dcrit ε / m.DlineAt ε ≤ m.DlineAt ε * (1 + c * ε ^ 2 + C * ε ^ 4) / m.DlineAt ε :=
      div_le_div_of_nonneg_right h1 hDl.le
    rw [mul_div_cancel_left₀ _ hDl.ne'] at this
    linarith

/-- **`D_crit = D_line (1 + O(ε²))` as `ε = 1/ω₀ → 0⁺`** (`R, X` fixed, `L = ε X`): for
`E ≠ 0`, `R, X, M > 0` and `K > 0`, `D_crit(ε)/D_line(ε) − 1 = O(ε²)` (the first-order form of
`VSM.Model.isBigO_Dcrit_sub`). -/
@[tmio M, powerlib_domain] theorem Model.isBigO_Dcrit (m : Model) (hE : m.g.E ≠ 0)
    (hR : 0 < m.g.R) (hX : 0 < m.g.X) (hM : 0 < m.g.M) (hK : 0 < m.K) :
    (fun ε => m.Dcrit ε / m.DlineAt ε - 1) =O[𝓝[>] 0] (fun ε => ε ^ 2) := by
  have h := m.isBigO_Dcrit_sub hE hR hX hM hK
  have h42 : (fun ε : ℝ => ε ^ 4) =O[𝓝[>] 0] (fun ε : ℝ => ε ^ 2) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε ⟨hε, hε1⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    exact pow_le_pow_of_le_one hε.le hε1.le (by norm_num)
  have hc : (fun ε : ℝ => m.DcritCoeff * ε ^ 2) =O[𝓝[>] 0] (fun ε : ℝ => ε ^ 2) :=
    isBigO_const_mul_self _ _ _
  refine ((h.trans h42).add hc).congr_left fun ε => ?_
  ring

/-- **The full model's boundary is `D_line (1 + O(ε²))`.** For a balanced physical model with
`R > 0` and `K > 0` there are `C > 0` and `ε₀ > 0` such that on every line of time scale
`ε ∈ (0, ε₀)` (same reactance, power curve and set-point) the model with damping
`D ≥ D_line(ε)(1 + C ε²)` is locally exponentially stable and the model with positive damping
`D ≤ D_line(ε)(1 − C ε²)` is unstable. (Its quasi-static swing reduction is stable for every
`D > 0`, `Synchronous.Swing.mem_den_locallyExponentiallyStable`; that is not part of this
statement.) -/
@[tmio TM, powerlib_domain] theorem Model.atScale_mem_den_sandwich (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) (hK : 0 < m.K) :
    connection% (∃ C : ℝ, 0 < C ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ D : ℝ, 0 < D →
      (m.DlineAt ε * (1 + C * ε ^ 2) ≤ D →
        m.atScale ε D ∈ family.den (.flow .locallyExponentiallyStable)) ∧
      (D ≤ m.DlineAt ε * (1 - C * ε ^ 2) → m.atScale ε D ∈ family.den (.flow .unstable))) := by
  unfold TMIO.Statement
  obtain ⟨hN, hM, -⟩ := hp
  have hX := hN.X_pos
  have hZ := hN.absSq_pos
  obtain ⟨C, hC, ε0, hε0, H⟩ := m.exists_routh_sandwich hN.E.ne' hR hX hM hK
  refine ⟨C, hC, ε0, hε0, fun ε hε hεε0 D hD => ?_⟩
  have hp' : Meets (m.atScale ε D) .physical :=
    ⟨⟨hN.E, hN.V, hN.R, mul_pos hε hX, one_div_pos.mpr hε⟩, hM, hD⟩
  have hb' : Meets (m.atScale ε D) .balanced := by
    change (m.atScale ε D).g.qssPower (m.atScale ε D).δ = m.g.Pref
    rw [atScale_qssPower m D hε.ne' hZ]; exact hb
  obtain ⟨Hup, Hdn⟩ := H ε hε hεε0 D hD
  exact ⟨fun h => mem_den_locallyExponentiallyStable _ hp' hb' (Hup h),
    fun h => mem_den_unstable _ hp' hb' (Hdn h)⟩

end VSM

end powerlib.GFM.Line
