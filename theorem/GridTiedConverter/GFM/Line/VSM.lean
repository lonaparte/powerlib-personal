import theorem.GridTiedConverter.GFM.Line.Model
import theorem.Criteria.Routh4
import theorem.Dynamics.ConverseLinearization
import theorem.Spectral.Local

/-! # The VSM on a dynamic R–L line: exact quartic, family, and the failure of the phasor model

The four-state VSM of `theorem/GridTiedConverter/GFM/Line/Model.lean` linearized at its
operating point: the characteristic polynomial derived from the `fderiv` Jacobian, its Routh
conditions as the model family `Line.VSM.family`, and the comparison with the quasi-static
(phasor) reduction, the swing family `Synchronous.Swing.family`: the reduced model can be stable
while the full model is unstable.

Model boundary.
* State `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive active power, the
  field `Line.VSM.field` (`M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`); its
  boundary is that of `theorem/GridTiedConverter/GFM/Line/Model.lean` (constant `E`, no inner
  loops, PLL, delay, PWM, LC filter).
* A model `Line.VSM.Model` is a parameter set with a selected angle `δ*`, read at the operating
  point `(δ*, 0, i_s(δ*))`; `Q = Q(δ*)`, `K = K(δ*) = P'(δ*)`, `κ = K + Q = E² X/|Z|²`,
  `σ = R/L`, `ρ = σ² + (X/L)²`.
* Level: local exponential stability / instability of the operating point by linearization
  (Routh–Hurwitz, degree four) and its converse; no global or transient claim.

Source: study note `gfm/t4-timescale/REPORT.md` ("Exact linear structure", (c) mechanism 1)
and its scripts `t4_02_charpoly.py`, `t4_04_vsm_boundary.py` (discovery evidence only); the
quartic Routh–Hurwitz criterion (`theorem/Criteria/Routh4.lean`).

Results.
* `VSM.characteristic_polynomial`: at every state,
  `M det(sI − J) = (M s² + D s − Q_e)(s² + 2σ s + ρ) + E² X/L²`; at the operating point
  (`Model.coeff0_eq`) the constant term is `ρ K/M`, i.e.
  `M det(sI − J) = (M s² + D s + K)((s + σ)² + ω₀²) − κ s (s + 2σ)`.
* Sum and product rules (`Model.trace_jac`, `Model.det_jac`): the trace and the determinant of the
  full Jacobian are those of the swing Jacobian of the reduced model and of the uncoupled line
  block `Network.lineJacobian` (trace `−2σ`, determinant `ρ`), added and multiplied: the slow
  modes gain exactly the real part the fast line modes lose.
* `Model.coeff1_eq`: the `s` coefficient is `(ρ (D − D_line) + 2σ K)/M` with the line damping
  `D_line = 2 E² R X L/|Z|⁴ = 2σκ/ρ` (`Network.Dline_eq`), the first-order correction of the
  slow manifold (`theorem/GridTiedConverter/GFM/Line/SlowManifold.lean`).

Family and connection conclusions.
* `Line.VSM.family`: static requirements `balanced` (`P(δ*) = P_ref`), `physical`
  (`Network.Physical`, `M, D > 0`), `routh` (the quartic Routh conditions `a₃, a₁, a₀ > 0`,
  `a₁² + a₃² a₀ < a₃ a₂ a₁` of the monic characteristic polynomial at the operating point) and
  `destabilizing` (their strict violation). The local sentences translate into
  `{balanced, physical, routh}`, instability into `{balanced, physical, destabilizing}`, passivity
  into nothing (exact), the remaining sentences into the whole, inconsistent, language
  (`VSM.realize_univ`); `VSM.chain_le_semantics` proves soundness. Within `physical` the local
  exponential translation is exact (`VSM.exactUnder_locallyExponentiallyStable`, converse
  linearization).
* `VSM.mem_den_locallyExponentiallyStable_iff`: the exact Routh boundary in closed form, for a
  balanced physical model: local exponential stability iff `K > 0`, `2σQ < Dρ` and
  `(2σM + D)² ρ K + M (Dρ − 2σQ)² < (2σM + D)(Mρ + 2σD − Q)(Dρ − 2σQ)` (cubic in `D`).
* `VSM.mem_den_unstable_of_K_neg`: `K < 0` makes `a₀ = ρK/M` negative, so the full model is
  unstable whenever its swing reduction is a saddle (no reverse disagreement there).
* Lossless line (`R = 0`): the third Hurwitz determinant is `−D² E² X/(L² M³) < 0`, so every
  balanced physical model is unstable (`VSM.mem_den_unstable_of_lossless`), and no model with
  `M, L, X > 0`, `E ≠ 0` is locally exponentially stable whatever its damping
  (`VSM.not_mem_den_locallyExponentiallyStable_of_lossless`).
* The phasor model is stable but the full model unstable
  (connection of `Line.VSM.family` and `Synchronous.Swing.family` through `VSM.Model.toSwing`,
  scaffold `theorem/GridTiedConverter/GFM/Line/LineReduction.agda`): every lossless balanced
  physical model with `K > 0` (`VSM.swing_stable_full_unstable_of_lossless`), and on the lossy line
  `E = V = R = L = ω₀ = M = 1` at zero load the boundary witnesses `VSM.lowDamping` (`D = 1/10`:
  reduced stable, full unstable, `VSM.lowDamping_swing_stable_full_unstable`) and
  `VSM.highDamping` (`D = 1`: the full model stable, `VSM.highDamping_stable`).
-/

noncomputable section
namespace powerlib.GFM.Line
open powerlib.Dynamics (State)
open Set

/-! ## Line constants -/

namespace Network

variable (N : Network)

/-- Decay rate of the line current, `σ = R/L`. -/
def σ : ℝ := N.R / N.L

/-- `ρ = σ² + (X/L)² = |Z|²/L²`, the squared modulus of the line poles `−σ ± j X/L`. -/
def ρ : ℝ := N.σ ^ 2 + (N.X / N.L) ^ 2

/-- Line damping `D_line = 2 E² R X L/|Z|⁴`. -/
def Dline : ℝ := 2 * N.E ^ 2 * N.R * N.X * N.L / N.absSq ^ 2

/-- The Jacobian of the uncoupled line current, `[[−σ, X/L], [−X/L, −σ]]`. -/
def lineJacobian : Matrix (Fin 2) (Fin 2) ℝ := !![-N.σ, N.X / N.L; -(N.X / N.L), -N.σ]

@[tmio M, powerlib_domain] theorem trace_lineJacobian : N.lineJacobian.trace = -2 * N.σ := by
  simp [lineJacobian, Matrix.trace_fin_two]; ring

@[tmio M, powerlib_domain] theorem det_lineJacobian : N.lineJacobian.det = N.ρ := by
  simp [lineJacobian, Matrix.det_fin_two, ρ]; ring

/-- `κ ρ = E² X/L²`. -/
@[tmio M, powerlib_domain] theorem κ_mul_ρ (hL : N.L ≠ 0) (hZ : N.absSq ≠ 0) :
    N.κ * N.ρ = N.E ^ 2 * N.X / N.L ^ 2 := by
  simp only [κ, ρ, σ]
  unfold absSq at hZ ⊢
  field_simp

/-- `D_line = 2σκ/ρ`. -/
@[tmio M, powerlib_domain] theorem Dline_eq (hL : N.L ≠ 0) (hZ : N.absSq ≠ 0) :
    N.Dline = 2 * N.σ * N.κ / N.ρ := by
  have hρ : N.ρ = N.absSq / N.L ^ 2 := by simp only [ρ, σ, absSq]; field_simp
  rw [hρ, Dline, κ, σ]
  field_simp

end Network

namespace VSM

variable (g : VSM)

/-! ## The characteristic polynomial -/

@[tmio M, powerlib_domain] private theorem trace_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).trace = -(2 * g.σ + g.D / g.M) := by
  simp [jacobian, Matrix.trace, Fin.sum_univ_four, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem minor2_jacobian (δ id iq : ℝ) :
    Criteria.principalMinorSum2Fin4 (g.jacobian δ id iq) =
      g.ρ + (2 * g.σ * g.D - g.reactive δ id iq) / g.M := by
  simp [Criteria.principalMinorSum2Fin4, jacobian, Network.ρ, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem minor3_jacobian (δ id iq : ℝ) :
    Criteria.principalMinorSum3Fin4 (g.jacobian δ id iq) =
      -((g.D * g.ρ - 2 * g.σ * g.reactive δ id iq) / g.M) := by
  simp [Criteria.principalMinorSum3Fin4, jacobian, Network.ρ, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem det_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).det =
      (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive δ id iq * g.ρ) / g.M := by
  rw [Criteria.det_fin_four]
  simp [jacobian, Network.ρ, Network.σ]
  linear_combination (g.E ^ 2 * g.X / (g.L ^ 2 * g.M)) * Real.sin_sq_add_cos_sq δ

/-- Monic coefficient of `s³`: `a₃ = 2σ + D/M`. -/
def coeff3 : ℝ := 2 * g.σ + g.D / g.M

/-- Monic coefficient of `s²` at reactive power `Q`: `a₂ = ρ + (2σD − Q)/M`. -/
def coeff2 (Q : ℝ) : ℝ := g.ρ + (2 * g.σ * g.D - Q) / g.M

/-- Monic coefficient of `s` at reactive power `Q`: `a₁ = (Dρ − 2σQ)/M`. -/
def coeff1 (Q : ℝ) : ℝ := (g.D * g.ρ - 2 * g.σ * Q) / g.M

/-- Monic constant coefficient at reactive power `Q`: `a₀ = (E² X/L² − Qρ)/M`. -/
def coeff0 (Q : ℝ) : ℝ := (g.E ^ 2 * g.X / g.L ^ 2 - Q * g.ρ) / g.M

/-- The monic characteristic polynomial of the Jacobian at any state, from the `fderiv`
Jacobian `VSM.jacobian` (`VSM.hasFDerivAt_field`). -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (δ id iq : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      s ^ 4 + (g.coeff3 : ℂ) * s ^ 3 + (g.coeff2 (g.reactive δ id iq) : ℂ) * s ^ 2 +
        (g.coeff1 (g.reactive δ id iq) : ℂ) * s + (g.coeff0 (g.reactive δ id iq) : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_four, trace_jacobian, minor2_jacobian,
    minor3_jacobian, det_jacobian, coeff3, coeff2, coeff1, coeff0]
  push_cast; ring

/-- **Characteristic polynomial**: `M det(sI − J) = (M s² + D s − Q_e)(s² + 2σ s + ρ) + E² X/L²`
at every state, `Q_e` the reactive power there. -/
@[tmio M, powerlib_domain] theorem characteristic_polynomial (hM : g.M ≠ 0) (δ id iq : ℝ)
    (s : ℂ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ)) *
        (s ^ 2 + ((2 * g.σ : ℝ) : ℂ) * s + (g.ρ : ℂ)) + ((g.E ^ 2 * g.X / g.L ^ 2 : ℝ) : ℂ) := by
  rw [det_characteristicMatrix, coeff3, coeff2, coeff1, coeff0]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp
  ring

/-! ## Models at the operating point -/

/-- Reactive power `Q = Q(δ*)` at the operating point. -/
def Model.Q (m : Model) : ℝ := m.g.qssReactive m.δ

/-- Synchronizing coefficient `K = P'(δ*)` at the operating point. -/
def Model.K (m : Model) : ℝ := m.g.syncCoeff m.δ

/-- The Jacobian at the operating point. -/
def Model.jac (m : Model) : Matrix (Fin 4) (Fin 4) ℝ :=
  m.g.jacobian m.δ (m.g.is m.δ).re (m.g.is m.δ).im

@[tmio M, powerlib_domain] theorem Model.fderiv_point (m : Model) :
    fderiv ℝ m.g.field m.point = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac := by
  rw [m.g.fderiv_field]
  simp [Model.point, qss, Model.jac]

/-- The monic characteristic polynomial at the operating point. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix (m : Model) (s : ℂ) :
    (Linear.characteristicMatrix m.jac s).det =
      s ^ 4 + (m.g.coeff3 : ℂ) * s ^ 3 + (m.g.coeff2 m.Q : ℂ) * s ^ 2 +
        (m.g.coeff1 m.Q : ℂ) * s + (m.g.coeff0 m.Q : ℂ) :=
  m.g.det_characteristicMatrix _ _ _ s

/-- At the operating point the constant coefficient is `ρ K/M` (`K + Q = κ`, `κ ρ = E² X/L²`). -/
@[tmio M, powerlib_domain] theorem Model.coeff0_eq (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) : m.g.coeff0 m.Q = m.g.ρ * m.K / m.g.M := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  have h2 := m.g.κ_mul_ρ hL hZ.ne'
  rw [coeff0, ← h2, Model.K, show m.g.syncCoeff m.δ = m.g.κ - m.Q by
    rw [Model.Q]; linarith]
  ring

/-- The `s` coefficient through the line damping: `a₁ = (ρ (D − D_line) + 2σ K)/M`. -/
@[tmio M, powerlib_domain] theorem Model.coeff1_eq (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.g.coeff1 m.Q = (m.g.ρ * (m.g.D - m.g.Dline) + 2 * m.g.σ * m.K) / m.g.M := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  rw [coeff1, m.g.Dline_eq hL hZ.ne', Model.K, show m.Q = m.g.κ - m.g.syncCoeff m.δ by
    rw [Model.Q]; linarith]
  field_simp
  ring

/-- **Sum rule**: `tr J = tr J_swing + tr J_line` — the trace of the full Jacobian is that of the
reduced swing Jacobian plus that of the uncoupled line. -/
@[tmio M, powerlib_domain] theorem Model.trace_jac (m : Model) :
    m.jac.trace = (m.g.swingParams.jacobian m.δ).trace + m.g.lineJacobian.trace := by
  rw [Model.jac, trace_jacobian, Synchronous.SwingParams.trace_jacobian,
    Network.trace_lineJacobian]
  simp [swingParams]; ring

/-- **Product rule**: `det J = det J_swing · det J_line` (`hL`, `|Z|² > 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_jac (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.jac.det = (m.g.swingParams.jacobian m.δ).det * m.g.lineJacobian.det := by
  rw [Model.jac, det_jacobian, Synchronous.SwingParams.det_jacobian, Network.det_lineJacobian,
    ← coeff0, show m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q from rfl,
    m.coeff0_eq hL hZ]
  simp [swingParams, Model.K, Network.syncCoeff, Synchronous.SwingParams.syncCoeff]; ring

/-! ## The family -/

/-- Static requirements on VSM-on-line models. -/
inductive Requirement
  /-- Power balance at the selected angle: `P(δ*) = P_ref`. -/
  | balanced
  /-- Physical network (`Network.Physical`), positive inertia and damping. -/
  | physical
  /-- The quartic Routh conditions of the monic characteristic polynomial at the operating
  point. -/
  | routh
  /-- A strict violation of a quartic Routh sign condition. -/
  | destabilizing

/-- The quartic Routh conditions `a₃, a₁, a₀ > 0`, `a₁² + a₃² a₀ < a₃ a₂ a₁` at the operating
point. -/
def Model.Routh (m : Model) : Prop :=
  0 < m.g.coeff3 ∧ 0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
    m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q <
      m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q

/-- Their strict violation: a negative coefficient or a negative third Hurwitz determinant. -/
def Model.RouthViolation (m : Model) : Prop :=
  m.g.coeff3 < 0 ∨ m.g.coeff2 m.Q < 0 ∨ m.g.coeff1 m.Q < 0 ∨ m.g.coeff0 m.Q < 0 ∨
    m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q <
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.g.qssPower m.δ = m.g.Pref
  | .physical => m.g.Physical ∧ 0 < m.g.M ∧ 0 < m.g.D
  | .routh => m.Routh
  | .destabilizing => m.RouthViolation

/-- The translation of the sentences: the local ones into balance, physical parameters and the
Routh conditions; instability into balance, physical parameters and a strict violation;
passivity into nothing; every other sentence into the whole, inconsistent, language. -/
abbrev translate : Sentence → Set Requirement :=
  Spectral.localTable {.balanced, .physical, .routh} {.balanced, .physical, .routh}
    {.balanced, .physical, .destabilizing} ∅

/-- The VSM-on-line family. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.g.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.g.field) (pt := Model.point)
    family_isAutonomous

@[tmio M, powerlib_domain] private theorem equilibrium_of {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.g.field m.point = 0 :=
  (m.field_point_eq_zero_iff hp.2.1.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb

/-- Balance, physical parameters and the Routh conditions place a model in local exponential
stability (the Jacobian at the operating point is Hurwitz, quartic Routh–Hurwitz). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hr : m.Routh) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact hurwitz_linearization_locally_exponentially_stable m.jac m.g.contDiff_field
    (equilibrium_of hp hb) m.fderiv_point
    ((Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
      m.det_characteristicMatrix).mpr hr)

/-- Balance, physical parameters and a strict Routh violation place a model in instability (a
characteristic root in the open right half plane). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hv : m.RouthViolation) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact unstable_of_exists_complex_eigenvalue_re_pos m.jac m.g.contDiff_field
    (equilibrium_of hp hb) m.fderiv_point
    (Criteria.exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation _
      m.det_characteristicMatrix hv)

/-- The whole requirement language is inconsistent: the Routh conditions exclude their strict
violation. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  obtain ⟨h3, h1, h0, hg⟩ : m.Routh := h .routh
  have h2 := Criteria.quartic_routh_a2_pos h3 h1 h0 hg
  rcases (h .destabilizing : m.RouthViolation) with v | v | v | v | v <;> linarith

/-- Every translation of the VSM-on-line family is sound: the quartic Routh conditions prove the
local sentences, a strict violation proves instability, and passivity holds without
requirement. -/
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
Hurwitz, i.e. meets the quartic Routh conditions (converse linearization). -/
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
    (m.field_point_eq_zero_iff hp.2.1.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mp heq
  have hr : m.Routh :=
    (Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _ m.det_characteristicMatrix).mp hH
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl | rfl)
  · exact hb
  · exact hp
  · exact hr

/-! ## The exact Routh boundary -/

@[tmio M, powerlib_domain] private theorem routh_iff {m : Model} (hp : Meets m .physical) :
    m.Routh ↔ 0 < m.K ∧ 2 * m.g.σ * m.Q < m.g.D * m.g.ρ ∧
      (2 * m.g.σ * m.g.M + m.g.D) ^ 2 * (m.g.ρ * m.K) +
          m.g.M * (m.g.D * m.g.ρ - 2 * m.g.σ * m.Q) ^ 2 <
        (2 * m.g.σ * m.g.M + m.g.D) * (m.g.M * m.g.ρ + 2 * m.g.σ * m.g.D - m.Q) *
          (m.g.D * m.g.ρ - 2 * m.g.σ * m.Q) := by
  obtain ⟨hN, hM, hD⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; positivity
  have hσ : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
  have h3 : 0 < m.g.coeff3 := by unfold coeff3; positivity
  have e0 := m.coeff0_eq hL hZ
  have eA : m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q =
      ((2 * m.g.σ * m.g.M + m.g.D) ^ 2 * (m.g.ρ * m.K) +
        m.g.M * (m.g.D * m.g.ρ - 2 * m.g.σ * m.Q) ^ 2) / m.g.M ^ 3 := by
    rw [e0, coeff1, coeff3]; field_simp; ring
  have eB : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      (2 * m.g.σ * m.g.M + m.g.D) * (m.g.M * m.g.ρ + 2 * m.g.σ * m.g.D - m.Q) *
        (m.g.D * m.g.ρ - 2 * m.g.σ * m.Q) / m.g.M ^ 3 := by
    rw [coeff3, coeff2, coeff1]; field_simp; ring
  unfold Model.Routh
  rw [eA, eB, div_lt_div_iff_of_pos_right (by positivity), e0, coeff1,
    div_pos_iff_of_pos_right hM, div_pos_iff_of_pos_right hM, sub_pos]
  constructor
  · rintro ⟨-, h1, h0, hg⟩
    exact ⟨pos_of_mul_pos_right h0 hρ.le, h1, hg⟩
  · rintro ⟨hK, h1, hg⟩
    exact ⟨h3, h1, mul_pos hρ hK, hg⟩

/-- **Exact Routh boundary in closed form**: a balanced model with physical parameters is
locally exponentially stable iff `K > 0`, `2σQ < Dρ` and
`(2σM + D)² ρ K + M (Dρ − 2σQ)² < (2σM + D)(Mρ + 2σD − Q)(Dρ − 2σQ)` — a cubic inequality in
the damping `D` (exactness `VSM.exactUnder_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      0 < m.K ∧ 2 * m.g.σ * m.Q < m.g.D * m.g.ρ ∧
        (2 * m.g.σ * m.g.M + m.g.D) ^ 2 * (m.g.ρ * m.K) +
            m.g.M * (m.g.D * m.g.ρ - 2 * m.g.σ * m.Q) ^ 2 <
          (2 * m.g.σ * m.g.M + m.g.D) * (m.g.M * m.g.ρ + 2 * m.g.σ * m.g.D - m.Q) *
            (m.g.D * m.g.ρ - 2 * m.g.σ * m.Q)) := by
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
the constant coefficient `ρ K/M` negative, so a balanced physical model with `K < 0` is unstable
(as is its swing reduction). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_K_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m hp hb (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
  have hZ := hp.1.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hp.1.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hp.1.L 2)
  rw [m.coeff0_eq hp.1.L.ne' hZ]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hρ hK) hp.2.1

/-! ## The lossless line -/

/-- Lossless line: the third Hurwitz determinant of the quartic is `−D² E² X/(L² M³)`. -/
@[tmio M, powerlib_domain] theorem hurwitzDet_of_lossless (hR : g.R = 0) (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) (Q : ℝ) :
    g.coeff3 * g.coeff2 Q * g.coeff1 Q - (g.coeff1 Q ^ 2 + g.coeff3 ^ 2 * g.coeff0 Q) =
      -(g.D ^ 2 * g.E ^ 2 * g.X / (g.L ^ 2 * g.M ^ 3)) := by
  simp only [coeff3, coeff2, coeff1, coeff0, Network.ρ, Network.σ, hR]
  field_simp
  ring

/-- **Lossless line, VSM**: every balanced model with physical parameters and `R = 0` is
unstable (the third Hurwitz determinant `−D² E² X/(L² M³)` is negative). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_lossless (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨hN, hM, hD⟩ := hp
  refine mem_den_unstable m ⟨hN, hM, hD⟩ hb (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  have h := m.g.hurwitzDet_of_lossless hR hM.ne' hN.L.ne' m.Q
  have : 0 < m.g.D ^ 2 * m.g.E ^ 2 * m.g.X / (m.g.L ^ 2 * m.g.M ^ 3) := by
    have := hN.X_pos; have := hN.E; have := hN.L; positivity
  linarith

/-- **Lossless line, VSM, any damping**: with `R = 0`, `M, L, X > 0` and `E ≠ 0` no model is
locally exponentially stable: a Hurwitz Jacobian would need `a₁ = Dρ/M > 0`, hence `D ≠ 0`, and
then the third Hurwitz determinant is negative (converse linearization). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_lossless
    (m : Model) (hR : m.g.R = 0) (hM : 0 < m.g.M) (hL : 0 < m.g.L) (hX : 0 < m.g.X)
    (hE : m.g.E ≠ 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  intro hs
  rw [mem_den_flow_iff] at hs
  obtain ⟨-, hH⟩ := (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian m.jac
    m.g.contDiff_field m.fderiv_point).mp hs
  obtain ⟨-, h1, -, hg⟩ :=
    (Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _ m.det_characteristicMatrix).mp hH
  have hD : m.g.D ≠ 0 := by
    rintro hD
    simp [coeff1, hD, Network.σ, hR] at h1
  have h := m.g.hurwitzDet_of_lossless hR hM.ne' hL.ne' m.Q
  have : 0 < m.g.D ^ 2 * m.g.E ^ 2 * m.g.X / (m.g.L ^ 2 * m.g.M ^ 3) := by positivity
  linarith

/-! ## The phasor model stable, the full model unstable -/

/-- **Phasor model stable, full model unstable (lossless line)**: a balanced model with physical
parameters, `R = 0` and `K > 0` has a locally exponentially stable quasi-static (swing) reduction
and is itself unstable. -/
@[tmio TM, powerlib_domain] theorem swing_stable_full_unstable_of_lossless (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) (hK : 0 < m.K) :
    connection% (m.toSwing ∈ Synchronous.Swing.family.den (.flow .locallyExponentiallyStable) ∧
      m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  refine ⟨?_, mem_den_unstable_of_lossless m hp hb hR⟩
  have hZ := hp.1.absSq_pos
  refine Synchronous.Swing.mem_den_locallyExponentiallyStable m.toSwing hp.2.1 hp.2.2 ?_ hK
  change m.g.c0 + m.g.A * Real.sin (m.δ - m.g.α) = m.g.Pref
  rw [← m.g.qssPower_eq_polar hZ]; exact hb

/-- The lossy line `E = V = R = L = ω₀ = 1` (`X = 1`, `|Z|² = 2`) with `M = 1`, damping `D`
and zero set-point, read at `δ* = 0`: the zero-load point, current `i_s(0) = 0`, `Q = 0`,
`K = κ = 1/2`, `σ = 1`, `ρ = 2`. -/
def lossyWitness (D : ℝ) : Model := ⟨⟨⟨1, 1, 1, 1, 1⟩, 1, D, 0⟩, 0⟩

/-- The witness below the boundary, `D = 1/10`. -/
def lowDamping : Model := lossyWitness (1 / 10)

/-- The witness above the boundary, `D = 1`. -/
def highDamping : Model := lossyWitness 1

@[tmio M, powerlib_domain] private theorem lossyWitness_physical {D : ℝ} (hD : 0 < D) :
    Meets (lossyWitness D) .physical :=
  ⟨⟨by norm_num [lossyWitness], by norm_num [lossyWitness], by norm_num [lossyWitness],
    by norm_num [lossyWitness], by norm_num [lossyWitness]⟩, by norm_num [lossyWitness], hD⟩

@[tmio M, powerlib_domain] private theorem lossyWitness_is (D : ℝ) :
    (lossyWitness D).g.is 0 = 0 := by
  simp [Network.is, lossyWitness]

@[tmio M, powerlib_domain] private theorem lossyWitness_balanced (D : ℝ) :
    Meets (lossyWitness D) .balanced := by
  change (lossyWitness D).g.qssPower 0 = 0
  simp [Network.qssPower, lossyWitness_is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem lossyWitness_Q (D : ℝ) : (lossyWitness D).Q = 0 := by
  change (lossyWitness D).g.qssReactive 0 = 0
  simp [Network.qssReactive, lossyWitness_is, Network.reactive_eq]

@[tmio M, powerlib_domain] private theorem lossyWitness_K (D : ℝ) :
    (lossyWitness D).K = 1 / 2 := by
  have hZ : 0 < (lossyWitness D).g.absSq := by norm_num [Network.absSq, Network.X, lossyWitness]
  have h := (lossyWitness D).g.syncCoeff_add_qssReactive hZ 0
  have hQ : (lossyWitness D).g.qssReactive 0 = 0 := lossyWitness_Q D
  change (lossyWitness D).g.syncCoeff 0 = 1 / 2
  rw [hQ, add_zero] at h
  rw [h]; norm_num [Network.κ, Network.absSq, Network.X, lossyWitness]

/-- **Boundary witness below the boundary**: at `D = 1/10` the quasi-static (swing) reduction is
locally exponentially stable while the full model is unstable. -/
@[tmio TM, powerlib_domain] theorem lowDamping_swing_stable_full_unstable :
    connection% (lowDamping.toSwing ∈
        Synchronous.Swing.family.den (.flow .locallyExponentiallyStable) ∧
      lowDamping ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  have hp := lossyWitness_physical (D := 1 / 10) (by norm_num)
  have hb := lossyWitness_balanced (1 / 10)
  refine ⟨?_, mem_den_unstable lowDamping hp hb ?_⟩
  · have hZ := hp.1.absSq_pos
    refine Synchronous.Swing.mem_den_locallyExponentiallyStable lowDamping.toSwing hp.2.1 hp.2.2
      ?_ ?_
    · change lowDamping.g.c0 + lowDamping.g.A * Real.sin (lowDamping.δ - lowDamping.g.α) =
        lowDamping.g.Pref
      rw [← lowDamping.g.qssPower_eq_polar hZ]; exact hb
    · change 0 < lowDamping.K
      rw [lowDamping, lossyWitness_K]; norm_num
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [lowDamping, lossyWitness_Q]
    norm_num [coeff3, coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X, lossyWitness]

/-- **Boundary witness above the boundary**: at `D = 1` the full model is locally exponentially
stable (and so is its quasi-static reduction). -/
@[tmio TM, powerlib_domain] theorem highDamping_stable :
    connection% (highDamping ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  refine mem_den_locallyExponentiallyStable highDamping (lossyWitness_physical (by norm_num))
    (lossyWitness_balanced 1) ?_
  rw [Model.Routh, highDamping, lossyWitness_Q]
  norm_num [coeff3, coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X, lossyWitness]

end VSM

end powerlib.GFM.Line
