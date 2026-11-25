import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.Criteria.Routh3

/-! # Power synchronization on a dynamic R–L line: exact cubic, critical droop gain, family

The three-state power-synchronization (pure droop) law of
`theorem/GridTiedConverter/GFM/Line/Model.lean` linearized at its operating point: the
characteristic cubic derived from the `fderiv` Jacobian, the model family `Line.PSC.family`, the
exact Routh boundary in the gain and the critical droop gain, and the comparison with the
quasi-static law `GFM.PSC` (`theorem/GridTiedConverter/GFM/PSC.lean`), which excludes the
inductor dynamics: the phasor model can be stable while the full model is unstable.

Model boundary.
* State `(δ, i_d, i_q) : State 3`, grid dq frame at `ω₀`, export-positive active power, the field
  `Line.PSC.field` (`δ̇ = K_p (P_ref − P_e)`, `L i̇ = E e^{jδ} − V − (R + jX) i`); boundary of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`; no active-resistance damping loop.
* A model `Line.PSC.Model` is read at the operating point `(δ*, i_s(δ*))`; `Q = Q(δ*)`,
  `K = P'(δ*)`, `κ = K + Q = E² X/|Z|²`, `σ = R/L`, `ρ = σ² + (X/L)²`. Droop gain `m_p` in per
  unit of frequency: `K_p = m_p ω₀`.
* Level: local exponential stability / instability of the operating point by linearization
  (Routh–Hurwitz, degree three) and its converse.

Source: study note `gfm/t4-timescale/REPORT.md` ((c) mechanism 2) and its script
`t4_05_psc_boundary.py` (discovery evidence only); the cubic Routh–Hurwitz criterion
(`theorem/Criteria/Routh3.lean`).

Results.
* `PSC.characteristic_polynomial`: at every state
  `det(sI − J) = (s − K_p Q_e)(s² + 2σ s + ρ) + K_p E² X/L²`; at the operating point the constant
  term is `K_p ρ K` (`Model.coeff0_eq`).
* `Network.KpCrit = 2σ/κ`, `Network.KpCrit_eq`: `K_p,crit = 2 R ω₀ (1 + (R/X)²)/E²`, i.e. the
  critical droop gain `m_p,crit = 2 R (1 + (R/X)²)/E²`.

Family and connection conclusions.
* `Line.PSC.family`: requirements `balanced`, `physical` (`Network.Physical`, `K_p > 0`),
  `routh` (`a₂, a₀ > 0`, `a₀ < a₂ a₁`) and `destabilizing` (a strict violation), with the
  translation pattern of `theorem/GridTiedConverter/GFM/Line/VSM.lean`; soundness
  `PSC.chain_le_semantics`, exactness within `physical`
  `PSC.exactUnder_locallyExponentiallyStable`.
* `PSC.mem_den_locallyExponentiallyStable_iff` (exact Routh boundary in the gain): a balanced
  physical model is locally exponentially stable iff `K > 0`, `K_p Q < 2σ` and
  `2σ Q² K_p² − (4σ² Q + ρ κ) K_p + 2σρ > 0`;
  `PSC.mem_den_locallyExponentiallyStable_iff_of_reactive_zero`: at `Q = 0` iff `K > 0` and
  `K_p < K_p,crit`.
* `PSC.mem_den_unstable_of_K_neg`: `K < 0` makes `a₀ = K_p ρ K` negative (unstable).
* Lossless line (`R = 0`): `a₂ a₁ − a₀ = −K_p E² X/L² < 0`, every balanced physical model is
  unstable (`PSC.mem_den_unstable_of_lossless`) and no model with `K_p, L, X > 0`, `E ≠ 0` is
  locally exponentially stable (`PSC.not_mem_den_locallyExponentiallyStable_of_lossless`).
* The phasor model stable, the full model unstable (connection of `Line.PSC.family` and
  `GFM.PSC.family` through `PSC.Model.toPSC`, the reduced law in the angle `δ − α`,
  `PSC.reducedRhs_eq_shift`; scaffold `theorem/GridTiedConverter/GFM/Line/LineReduction.agda`):
  every lossless model (`PSC.psc_stable_full_unstable_of_lossless`) and every zero-reactive-power
  model above the critical gain (`PSC.psc_stable_full_unstable_of_gain`); boundary witnesses on
  the line `E = V = R = L = ω₀ = 1` at zero load (`K_p,crit = 4`): `PSC.lowGain_stable`
  (`K_p = 1`) and `PSC.highGain_psc_stable_full_unstable` (`K_p = 5`).
* On the Routh boundary itself (`theorem/GridTiedConverter/GFM/HopfLinePSC.lean`): the Hopf
  boundary `a₂ a₁ = a₀`, the first Lyapunov coefficient in closed form at every angle
  (`PSC.Model.firstLyapunov_crit`), its sign law (`PSC.Model.sign_firstLyapunov_crit`), the
  supercritical / subcritical connection theorems, the non-exactness of the local asymptotic and
  of the instability translations (`PSC.not_exactUnder_locallyAsymptoticallyStable`: the
  zero-load model at the critical gain `K_p = 4` is locally asymptotically stable;
  `PSC.not_exactUnder_unstable`); at the fold `K = 0` (`a₀ = 0`, a zero eigenvalue) the null
  pair, the fold coefficient in closed form and the saddle-node law (`PSC.Model.foldCoeff_fold`,
  `PSC.mem_den_unstable_of_fold`, `PSC.mem_den_unstable_of_fold_of_ne`);
  the complete Lyapunov and local asymptotic membership off the remaining degenerate set
  (`PSC.mem_den_lyapunovStable_iff`, `PSC.mem_den_locallyAsymptoticallyStable_iff`). The gain
  family, its transversality coefficient (`PSC.Model.paramTrace_gainJac_crit`) and the Hopf cycles
  along the gain: `theorem/GridTiedConverter/GFM/LinePSCHopfCycle.lean`.
-/

noncomputable section
namespace powerlib.GFM.Line
open powerlib.Dynamics (State)
open Set

namespace Network

variable (N : Network)

/-- The critical power-synchronization gain at zero reactive power, `K_p,crit = 2σ/κ`. -/
def KpCrit : ℝ := 2 * N.σ / N.κ

/-- `K_p,crit = 2 R ω₀ (1 + (R/X)²)/E²`: the critical droop gain is
`m_p,crit = K_p,crit/ω₀ = 2 R (1 + (R/X)²)/E²`. -/
@[tmio M, powerlib_domain] theorem KpCrit_eq (hL : N.L ≠ 0) (hω : N.ω0 ≠ 0) (hE : N.E ≠ 0) :
    N.KpCrit = 2 * N.R * N.ω0 * (1 + (N.R / N.X) ^ 2) / N.E ^ 2 := by
  have hX : N.X ≠ 0 := mul_ne_zero hω hL
  simp only [KpCrit, σ, κ, absSq]
  rw [show N.X = N.ω0 * N.L from rfl] at hX ⊢
  field_simp
  ring

end Network

namespace PSC

variable (g : PSC)

/-! ## The characteristic polynomial -/

@[tmio M, powerlib_domain] private theorem trace_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).trace = g.Kp * g.reactive δ id iq - 2 * g.σ := by
  simp [jacobian, Matrix.trace_fin_three, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem minor_jacobian (δ id iq : ℝ) :
    Criteria.principalMinorSum (g.jacobian δ id iq) =
      g.ρ - 2 * g.σ * (g.Kp * g.reactive δ id iq) := by
  simp [Criteria.principalMinorSum, jacobian, Network.ρ, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem det_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).det =
      -(g.Kp * (g.E ^ 2 * g.X / g.L ^ 2 - g.reactive δ id iq * g.ρ)) := by
  simp [jacobian, Matrix.det_fin_three, Network.ρ, Network.σ]
  linear_combination (-(g.Kp * g.E ^ 2 * g.X / g.L ^ 2)) * Real.sin_sq_add_cos_sq δ

/-- Monic coefficient of `s²` at reactive power `Q`: `a₂ = 2σ − K_p Q`. -/
def coeff2 (Q : ℝ) : ℝ := 2 * g.σ - g.Kp * Q

/-- Monic coefficient of `s` at reactive power `Q`: `a₁ = ρ − 2σ K_p Q`. -/
def coeff1 (Q : ℝ) : ℝ := g.ρ - 2 * g.σ * (g.Kp * Q)

/-- Monic constant coefficient at reactive power `Q`: `a₀ = K_p (E² X/L² − Q ρ)`. -/
def coeff0 (Q : ℝ) : ℝ := g.Kp * (g.E ^ 2 * g.X / g.L ^ 2 - Q * g.ρ)

/-- The monic characteristic polynomial of the Jacobian at any state, from the `fderiv` Jacobian
`PSC.jacobian` (`PSC.hasFDerivAt_field`). -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (δ id iq : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      s ^ 3 + (g.coeff2 (g.reactive δ id iq) : ℂ) * s ^ 2 +
        (g.coeff1 (g.reactive δ id iq) : ℂ) * s + (g.coeff0 (g.reactive δ id iq) : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_three', trace_jacobian, minor_jacobian,
    det_jacobian, coeff2, coeff1, coeff0]
  push_cast; ring

/-- **Characteristic polynomial**: `det(sI − J) = (s − K_p Q_e)(s² + 2σ s + ρ) + K_p E² X/L²` at
every state, `Q_e` the reactive power there. -/
@[tmio M, powerlib_domain] theorem characteristic_polynomial (δ id iq : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      (s - ((g.Kp * g.reactive δ id iq : ℝ) : ℂ)) *
        (s ^ 2 + ((2 * g.σ : ℝ) : ℂ) * s + (g.ρ : ℂ)) +
          ((g.Kp * (g.E ^ 2 * g.X / g.L ^ 2) : ℝ) : ℂ) := by
  rw [det_characteristicMatrix, coeff2, coeff1, coeff0]
  push_cast; ring

/-! ## Models at the operating point -/

/-- Reactive power `Q = Q(δ*)` at the operating point. -/
def Model.Q (m : Model) : ℝ := m.g.qssReactive m.δ

/-- Synchronizing coefficient `K = P'(δ*)` at the operating point. -/
def Model.K (m : Model) : ℝ := m.g.syncCoeff m.δ

/-- The Jacobian at the operating point. -/
def Model.jac (m : Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  m.g.jacobian m.δ (m.g.is m.δ).re (m.g.is m.δ).im

/-- The quasi-static PSC model of the reduced law, in the angle `δ − α`
(`PSC.reducedRhs_eq_shift`). -/
def Model.toPSC (m : Model) : powerlib.GFM.PSC.Model := ⟨m.g.toShifted, m.δ - m.g.α⟩

@[tmio M, powerlib_domain] theorem Model.fderiv_point (m : Model) :
    fderiv ℝ m.g.field m.point = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jac := by
  rw [m.g.fderiv_field]
  simp [Model.point, qss, Model.jac]

/-- The monic characteristic polynomial at the operating point. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix (m : Model) (s : ℂ) :
    (Linear.characteristicMatrix m.jac s).det =
      s ^ 3 + (m.g.coeff2 m.Q : ℂ) * s ^ 2 + (m.g.coeff1 m.Q : ℂ) * s + (m.g.coeff0 m.Q : ℂ) :=
  m.g.det_characteristicMatrix _ _ _ s

/-- At the operating point the constant coefficient is `K_p ρ K`. -/
@[tmio M, powerlib_domain] theorem Model.coeff0_eq (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) : m.g.coeff0 m.Q = m.g.Kp * (m.g.ρ * m.K) := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  have h2 := m.g.κ_mul_ρ hL hZ.ne'
  rw [coeff0, ← h2, Model.K, show m.g.syncCoeff m.δ = m.g.κ - m.Q by
    rw [Model.Q]; linarith]
  ring

/-- The Routh gap `a₂ a₁ − a₀` at the operating point, a quadratic in the gain:
`2σ Q² K_p² − (4σ² Q + ρ κ) K_p + 2σρ`. -/
@[tmio M, powerlib_domain] theorem Model.routhGap_eq (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.g.coeff2 m.Q * m.g.coeff1 m.Q - m.g.coeff0 m.Q =
      2 * m.g.σ * m.Q ^ 2 * m.g.Kp ^ 2 -
        (4 * m.g.σ ^ 2 * m.Q + m.g.ρ * m.g.κ) * m.g.Kp + 2 * m.g.σ * m.g.ρ := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  rw [m.coeff0_eq hL hZ, coeff2, coeff1, Model.K,
    show m.g.syncCoeff m.δ = m.g.κ - m.Q by rw [Model.Q]; linarith]
  ring

/-! ## The family -/

/-- Static requirements on PSC-on-line models. -/
inductive Requirement
  /-- Power balance at the selected angle: `P(δ*) = P_ref`. -/
  | balanced
  /-- Physical network (`Network.Physical`) and a positive gain. -/
  | physical
  /-- The cubic Routh conditions of the monic characteristic polynomial at the operating
  point. -/
  | routh
  /-- A strict violation of a cubic Routh sign condition. -/
  | destabilizing

/-- The cubic Routh conditions `a₂ > 0`, `a₀ > 0`, `a₀ < a₂ a₁` at the operating point. -/
def Model.Routh (m : Model) : Prop :=
  0 < m.g.coeff2 m.Q ∧ 0 < m.g.coeff0 m.Q ∧ m.g.coeff0 m.Q < m.g.coeff2 m.Q * m.g.coeff1 m.Q

/-- Their strict violation. -/
def Model.RouthViolation (m : Model) : Prop :=
  m.g.coeff2 m.Q < 0 ∨ m.g.coeff1 m.Q < 0 ∨ m.g.coeff0 m.Q < 0 ∨
    m.g.coeff2 m.Q * m.g.coeff1 m.Q < m.g.coeff0 m.Q

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.g.qssPower m.δ = m.g.Pref
  | .physical => m.g.Physical ∧ 0 < m.g.Kp
  | .routh => m.Routh
  | .destabilizing => m.RouthViolation

/-- The translation of the sentences: the local ones into balance, physical parameters and the
Routh conditions; instability into balance, physical parameters and a strict violation;
passivity into nothing; every other sentence into the whole, inconsistent, language. -/
abbrev translate : Sentence → Set Requirement :=
  Spectral.localTable {.balanced, .physical, .routh} {.balanced, .physical, .routh}
    {.balanced, .physical, .destabilizing} ∅

/-- The PSC-on-line family. -/
def family : Family Model Requirement 3 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.g.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.g.field) (pt := Model.point)
    family_isAutonomous

@[tmio M, powerlib_domain] private theorem equilibrium_of {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.g.field m.point = 0 :=
  (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb

@[tmio TM, powerlib_domain] private theorem isHurwitz_iff (m : Model) :
    LinearSystems.IsHurwitz m.jac ↔ m.Routh :=
  (Criteria.isHurwitz_iff_of_det_characteristicMatrix _
    (fun s => by rw [m.det_characteristicMatrix])).trans (Criteria.cubic_roots_re_neg_iff _ _ _)

/-- Balance, physical parameters and the Routh conditions place a model in local exponential
stability (cubic Routh–Hurwitz on the Jacobian at the operating point). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hr : m.Routh) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact hurwitz_linearization_locally_exponentially_stable m.jac m.g.contDiff_field
    (equilibrium_of hp hb) m.fderiv_point ((isHurwitz_iff m).mpr hr)

/-- Balance, physical parameters and a strict Routh violation place a model in instability. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hv : m.RouthViolation) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  obtain ⟨s, hs, hre⟩ := Criteria.exists_cubic_root_re_pos_of_violation hv
  exact Dynamics.unstable_of_characteristic_root_re_pos m.jac m.g.contDiff_field
    (equilibrium_of hp hb) m.fderiv_point (by rw [m.det_characteristicMatrix]; exact hs) hre

/-- The whole requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  obtain ⟨h2, h0, hg⟩ : m.Routh := h .routh
  have h1 : 0 < m.g.coeff1 m.Q := by
    by_contra h1
    push Not at h1
    nlinarith
  rcases (h .destabilizing : m.RouthViolation) with v | v | v | v <;> linarith

/-- Every translation of the PSC-on-line family is sound. -/
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

/-- Within physical parameters the local exponential translation is exact (converse
linearization). -/
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
    (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mp heq
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl | rfl)
  · exact hb
  · exact hp
  · exact (isHurwitz_iff m).mp hH

/-! ## The exact Routh boundary and the critical gain -/

@[tmio M, powerlib_domain] private theorem routh_iff {m : Model} (hp : Meets m .physical) :
    m.Routh ↔ 0 < m.K ∧ m.g.Kp * m.Q < 2 * m.g.σ ∧
      0 < 2 * m.g.σ * m.Q ^ 2 * m.g.Kp ^ 2 -
        (4 * m.g.σ ^ 2 * m.Q + m.g.ρ * m.g.κ) * m.g.Kp + 2 * m.g.σ * m.g.ρ := by
  obtain ⟨hN, hK⟩ := hp
  have hZ := hN.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hN.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have hg := m.routhGap_eq hN.L.ne' hZ
  have e0 := m.coeff0_eq hN.L.ne' hZ
  have e2 : m.g.coeff2 m.Q = 2 * m.g.σ - m.g.Kp * m.Q := rfl
  unfold Model.Routh
  rw [e0] at hg ⊢
  constructor
  · rintro ⟨h2, h0, h⟩
    exact ⟨pos_of_mul_pos_right (pos_of_mul_pos_right h0 hK.le) hρ.le, by linarith,
      by linarith⟩
  · rintro ⟨h0, h2, h⟩
    exact ⟨by linarith, mul_pos hK (mul_pos hρ h0), by linarith⟩

/-- **Exact Routh boundary in the gain**: a balanced model with physical parameters is locally
exponentially stable iff `K > 0`, `K_p Q < 2σ` and
`2σ Q² K_p² − (4σ² Q + ρ κ) K_p + 2σρ > 0` (exactness
`PSC.exactUnder_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      0 < m.K ∧ m.g.Kp * m.Q < 2 * m.g.σ ∧
        0 < 2 * m.g.σ * m.Q ^ 2 * m.g.Kp ^ 2 -
          (4 * m.g.σ ^ 2 * m.Q + m.g.ρ * m.g.κ) * m.g.Kp + 2 * m.g.σ * m.g.ρ) := by
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

/-- **Critical gain**: at zero reactive power a balanced physical model is locally
exponentially stable iff `K > 0` and `K_p < K_p,crit = 2σ/κ`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_reactive_zero
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hQ : m.Q = 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      0 < m.K ∧ m.g.Kp < m.g.KpCrit) := by
  have h := mem_den_locallyExponentiallyStable_iff m hp hb
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h, hQ]
  obtain ⟨hN, hK⟩ := hp
  have hZ := hN.absSq_pos
  have hκ : 0 < m.g.κ := by
    have := hN.X_pos; have := hN.E; unfold Network.κ; positivity
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hN.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  rw [Network.KpCrit, lt_div_iff₀ hκ]
  constructor
  · rintro ⟨h0, -, h⟩
    refine ⟨h0, ?_⟩
    nlinarith
  · rintro ⟨h0, h⟩
    refine ⟨h0, by nlinarith, by nlinarith⟩

/-- **No reverse disagreement on the saddle side**: `K < 0` makes the constant coefficient
`K_p ρ K` negative, so a balanced physical model with `K < 0` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_K_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m hp hb (Or.inr (Or.inr (Or.inl ?_)))
  have hZ := hp.1.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hp.1.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hp.1.L 2)
  rw [m.coeff0_eq hp.1.L.ne' hZ]
  exact mul_neg_of_pos_of_neg hp.2 (mul_neg_of_pos_of_neg hρ hK)

/-! ## The lossless line -/

/-- Lossless line: the Routh gap is `a₂ a₁ − a₀ = −K_p E² X/L²` at every reactive power. -/
@[tmio M, powerlib_domain] theorem routhGap_of_lossless (hR : g.R = 0) (Q : ℝ) :
    g.coeff2 Q * g.coeff1 Q - g.coeff0 Q = -(g.Kp * (g.E ^ 2 * g.X / g.L ^ 2)) := by
  simp only [coeff2, coeff1, coeff0, Network.ρ, Network.σ, hR]
  ring

/-- **Lossless line, PSC**: every balanced model with physical parameters and `R = 0` is
unstable, whatever the gain. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_lossless (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m hp hb (Or.inr (Or.inr (Or.inr ?_)))
  have h := m.g.routhGap_of_lossless hR m.Q
  have : 0 < m.g.Kp * (m.g.E ^ 2 * m.g.X / m.g.L ^ 2) := by
    have := hp.1.X_pos; have := hp.1.E; have := hp.1.L; have := hp.2; positivity
  linarith

/-- **Lossless line, PSC, any operating point**: with `R = 0`, `K_p, L, X > 0` and `E ≠ 0` no
model is locally exponentially stable (converse linearization: a Hurwitz Jacobian would need a
positive Routh gap). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_lossless
    (m : Model) (hR : m.g.R = 0) (hK : 0 < m.g.Kp) (hL : 0 < m.g.L) (hX : 0 < m.g.X)
    (hE : m.g.E ≠ 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  intro hs
  rw [mem_den_flow_iff] at hs
  obtain ⟨-, hH⟩ := (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian m.jac
    m.g.contDiff_field m.fderiv_point).mp hs
  obtain ⟨-, -, hg⟩ := (isHurwitz_iff m).mp hH
  have h := m.g.routhGap_of_lossless hR m.Q
  have : 0 < m.g.Kp * (m.g.E ^ 2 * m.g.X / m.g.L ^ 2) := by positivity
  linarith

/-! ## The phasor model stable, the full model unstable -/

@[tmio TM, powerlib_domain] private theorem toPSC_stable (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hK : 0 < m.K) :
    connection% (m.toPSC ∈ powerlib.GFM.PSC.family.den (.flow .locallyExponentiallyStable)) := by
  have hZ := hp.1.absSq_pos
  have hA : 0 < m.g.A := by
    have := hp.1.E; have := hp.1.V; exact div_pos (by positivity) (Real.sqrt_pos.mpr hZ)
  refine powerlib.GFM.PSC.locallyExponentiallyStable m.g.toShifted hp.2 hA ?_ ?_
  · have h := m.g.qssPower_eq_polar hZ m.δ
    change m.g.A * Real.sin (m.δ - m.g.α) = m.g.Pref - m.g.c0
    have hb' : m.g.qssPower m.δ = m.g.Pref := hb
    linarith
  · exact pos_of_mul_pos_right (show 0 < m.g.A * Real.cos (m.δ - m.g.α) from hK) hA.le

/-- **Phasor model stable, full model unstable (lossless line)**: a balanced physical model with
`R = 0` and `K > 0` has a locally exponentially stable quasi-static PSC reduction and is itself
unstable. -/
@[tmio TM, powerlib_domain] theorem psc_stable_full_unstable_of_lossless (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) (hK : 0 < m.K) :
    connection% (m.toPSC ∈ powerlib.GFM.PSC.family.den (.flow .locallyExponentiallyStable) ∧
      m ∈ family.den (.flow .unstable)) :=
  ⟨toPSC_stable m hp hb hK, mem_den_unstable_of_lossless m hp hb hR⟩

/-- **Phasor model stable, full model unstable (gain above the critical gain)**: a balanced
physical model at zero reactive power with `K > 0` and `K_p > K_p,crit` has a locally
exponentially stable quasi-static PSC reduction and is itself unstable. -/
@[tmio TM, powerlib_domain] theorem psc_stable_full_unstable_of_gain (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hQ : m.Q = 0) (hK : 0 < m.K)
    (hg : m.g.KpCrit < m.g.Kp) :
    connection% (m.toPSC ∈ powerlib.GFM.PSC.family.den (.flow .locallyExponentiallyStable) ∧
      m ∈ family.den (.flow .unstable)) := by
  refine ⟨toPSC_stable m hp hb hK, mem_den_unstable m hp hb (Or.inr (Or.inr (Or.inr ?_)))⟩
  obtain ⟨hN, hKp⟩ := hp
  have hZ := hN.absSq_pos
  have hκ : 0 < m.g.κ := by
    have := hN.X_pos; have := hN.E; unfold Network.κ; positivity
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hN.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have h := m.routhGap_eq hN.L.ne' hZ
  rw [hQ] at h ⊢
  rw [Network.KpCrit, div_lt_iff₀ hκ] at hg
  nlinarith

/-- The lossy line `E = V = R = L = ω₀ = 1` (`X = 1`, `|Z|² = 2`, `κ = 1/2`, `σ = 1`,
`K_p,crit = 4`) with gain `K_p` and zero set-point, read at `δ* = 0` (zero load, `Q = 0`,
`K = 1/2`). -/
def lossyWitness (Kp : ℝ) : Model := ⟨⟨⟨1, 1, 1, 1, 1⟩, Kp, 0⟩, 0⟩

/-- The witness below the critical gain, `K_p = 1`. -/
def lowGain : Model := lossyWitness 1

/-- The witness above the critical gain, `K_p = 5`. -/
def highGain : Model := lossyWitness 5

@[tmio M, powerlib_domain] private theorem lossyWitness_physical {Kp : ℝ} (hK : 0 < Kp) :
    Meets (lossyWitness Kp) .physical :=
  ⟨⟨by norm_num [lossyWitness], by norm_num [lossyWitness], by norm_num [lossyWitness],
    by norm_num [lossyWitness], by norm_num [lossyWitness]⟩, hK⟩

@[tmio M, powerlib_domain] private theorem lossyWitness_is (Kp : ℝ) :
    (lossyWitness Kp).g.is 0 = 0 := by
  simp [Network.is, lossyWitness]

@[tmio M, powerlib_domain] private theorem lossyWitness_balanced (Kp : ℝ) :
    Meets (lossyWitness Kp) .balanced := by
  change (lossyWitness Kp).g.qssPower 0 = 0
  simp [Network.qssPower, lossyWitness_is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem lossyWitness_Q (Kp : ℝ) : (lossyWitness Kp).Q = 0 := by
  change (lossyWitness Kp).g.qssReactive 0 = 0
  simp [Network.qssReactive, lossyWitness_is, Network.reactive_eq]

@[tmio M, powerlib_domain] private theorem lossyWitness_K (Kp : ℝ) :
    (lossyWitness Kp).K = 1 / 2 := by
  have hZ : 0 < (lossyWitness Kp).g.absSq := by
    norm_num [Network.absSq, Network.X, lossyWitness]
  have h := (lossyWitness Kp).g.syncCoeff_add_qssReactive hZ 0
  have hQ : (lossyWitness Kp).g.qssReactive 0 = 0 := lossyWitness_Q Kp
  change (lossyWitness Kp).g.syncCoeff 0 = 1 / 2
  rw [hQ, add_zero] at h
  rw [h]; norm_num [Network.κ, Network.absSq, Network.X, lossyWitness]

@[tmio M, powerlib_domain] private theorem lossyWitness_KpCrit (Kp : ℝ) :
    (lossyWitness Kp).g.KpCrit = 4 := by
  norm_num [Network.KpCrit, Network.σ, Network.κ, Network.absSq, Network.X, lossyWitness]

/-- **Boundary witness below the critical gain**: at `K_p = 1` the full model is locally
exponentially stable. -/
@[tmio TM, powerlib_domain] theorem lowGain_stable :
    connection% (lowGain ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_iff_of_reactive_zero lowGain
    (lossyWitness_physical (by norm_num)) (lossyWitness_balanced 1) (lossyWitness_Q 1)
  unfold TMIO.Statement at h ⊢
  rw [h, lowGain, lossyWitness_K, lossyWitness_KpCrit]
  norm_num [lossyWitness]

/-- **Boundary witness above the critical gain**: at `K_p = 5` the quasi-static PSC reduction is
locally exponentially stable while the full model is unstable. -/
@[tmio TM, powerlib_domain] theorem highGain_psc_stable_full_unstable :
    connection% (highGain.toPSC ∈
        powerlib.GFM.PSC.family.den (.flow .locallyExponentiallyStable) ∧
      highGain ∈ family.den (.flow .unstable)) :=
  psc_stable_full_unstable_of_gain highGain (lossyWitness_physical (by norm_num))
    (lossyWitness_balanced 5) (lossyWitness_Q 5)
    (by rw [highGain, lossyWitness_K]; norm_num)
    (by rw [highGain, lossyWitness_KpCrit]; norm_num [lossyWitness])

end PSC

end powerlib.GFM.Line
