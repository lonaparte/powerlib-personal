import theorem.GridTiedConverter.GFM.DCLink.Transfer
import theorem.Dynamics.Instability
import theorem.Dynamics.CascadeNode

/-! # The VSM on a dynamic line feeding its DC link: the nonlinear cascade (five states)

Model boundary.
* The five-state model `DynamicLine` of `theorem/GridTiedConverter/GFM/DCLink/Transfer.lean`:
  state `(δ, ω, i_d, i_q, V) : Dynamics.State 5`, in this order; the line VSM `Line.VSM` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean` (dq frame at `ω₀` aligned with the stiff grid
  `V_g ∠ 0`, line `L i̇ = E e^{jδ} − V_g − (R + jX) i`, `X = ω₀ L`, constant EMF magnitude `E`,
  `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`) feeding the DC node `C V̇ = (P_s + I_s V − P_e)/V`
  (`GFL.DCLink.nodeRate`) through the exported power `P_e = Re(E e^{jδ} conj i)`, at the constant
  power reference `P_ref` (DC-voltage loop open). The AC rows do not depend on `V`: the system
  is a cascade, line VSM first, DC node second.
* Signs: active and reactive power export-positive (the GFM convention of
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`); source power positive into the DC node.
* Continuous time, autonomous; parameters arbitrary reals. The field contains `1/V` and is `C¹`
  on the open set `V ≠ 0` (`DynamicLine.field_contDiffOn`). Excluded: the DC-voltage loop,
  reactive-power and amplitude loops, inner voltage and current loops, LC filter, limits, PLL,
  delay, PWM, DC-link losses; the singular plane `V = 0`.
* Level: local behaviour (local exponential and asymptotic stability, Lyapunov stability,
  instability) of the operating point `(δ*, 0, i_s(δ*), V*)`, from the Jacobian computed by
  `fderiv` (`DynamicLine.hasFDerivAt_field`) and the quartic Routh–Hurwitz criterion of the line
  VSM; not a basin estimate.

Source: GFM counterpart study, note T7 part (b) (`t7-dcside`, the dynamic-line DC plant; notes
outside the repository); the GFL counterpart is the current loop feeding the DC link,
`theorem/GridTiedConverter/GFL/DCLink/Cascade.lean` (`mem_den_locallyExponentiallyStable_iff`,
`mem_den_unstable_of_inverter`, `mem_den_locallyAsymptoticallyStable_iff`). Converse
linearization: `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`; the extra
pole: `Linear.spectrallyStable_iff_of_extra_pole`; quartic Routh–Hurwitz:
`Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic`. Scaffold:
`theorem/GridTiedConverter/GFM/DCLink/LineCascadeVSM.agda`.

Results.
* `DynamicLine.field_contDiffOn`: the five-state field is `C¹` on `V ≠ 0`.
* `LineCascade.Model.field_point_eq_zero_iff`: within regular parameters (`Model.Regular`:
  `V* ≠ 0`, `M, L, C ≠ 0`, `|Z|² > 0`) the operating point is an equilibrium iff it is balanced,
  `P(δ*) = P_ref` and `P_s + I_s V* = P(δ*)` (`Model.Balanced`; through the quasi-static reading,
  `DynamicLine.field_point_eq_zero_iff`).
* `LineCascade.Model.det_characteristicMatrix`: at a balanced point
  `det(sI − J) = det(sI − J_VSM)(s − b)`, `b = I_s/(C V*)` (`Model.b`), `J_VSM` the line-VSM
  Jacobian; `LineCascade.Model.isHurwitz_iff`: `J` is Hurwitz iff the line VSM meets its quartic
  Routh conditions (`Line.VSM.Model.Routh`) and `b < 0`.

Family and connection conclusions.
* `LineCascade.family := Spectral.localFamily Model.field Model.Stable Model.Unstable`: a model
  (`LineCascade.Model`) is a dynamic line with a selected angle `δ*` and DC voltage `V*`, read as
  the field translated so that `(δ*, 0, i_s(δ*), V*)` is the origin. `Model.Stable`: regular,
  balanced, the line-VSM Routh conditions and `b < 0`; `Model.Unstable`: regular, balanced and a
  strict line-VSM Routh violation or `b > 0`. Soundness `LineCascade.chain_le_semantics`.
* **Exact local exponential stability** (`LineCascade.mem_den_locallyExponentiallyStable_iff`,
  within regular parameters): locally exponentially stable iff balanced, the line VSM meets its
  quartic Routh conditions and `I_s/(C V*) < 0`; the translation is exact within regular
  parameters (`LineCascade.realize_eq_den_inter`). Read through the line-VSM family
  (`LineCascade.mem_den_locallyExponentiallyStable_iff_vsm`, physical network, `M, D > 0`,
  `C, V* ≠ 0`): the cascade is locally exponentially stable iff it is balanced, its AC part
  `Model.toVSM` is a locally exponentially stable member of `Line.VSM.family` (explicit cubic
  boundary `Line.VSM.mem_den_locallyExponentiallyStable_iff`) and `I_s/(C V*) < 0` — the GFM
  counterpart of the GFL cascade decision (current loop stable and rectifier mode).
* Instability: `LineCascade.mem_den_unstable` (a strict line-VSM Routh violation or `b > 0`);
  `LineCascade.mem_den_unstable_of_export`: with a constant-current source (`P_s = 0`, `C, V* > 0`)
  an exporting balanced point (`P(δ*) > 0`) is unstable whatever the AC part (the DC pole
  `b = P(δ*)/(C V*²) > 0`; GFL `Cascade.mem_den_unstable_of_inverter`).
* Necessity, boundaries included: `LineCascade.closedRouth_of_mem_den_lyapunovStable` (within
  regular parameters, Lyapunov stable ⇒ balanced, no strict line-VSM Routh violation, `b ≤ 0`);
  `LineCascade.not_mem_den_locallyAsymptoticallyStable_of_Is_eq_zero` (a constant-power source,
  `I_s = 0`, at a balanced point: the DC voltage is a line of equilibria); hence
  `LineCascade.closedRouth_of_mem_den_locallyAsymptoticallyStable` (local asymptotic stability ⇒
  balanced, no strict violation, `b < 0`).
* **Local asymptotic and Lyapunov stability off the line-VSM Routh boundary**
  (`LineCascade.mem_den_locallyAsymptoticallyStable_iff_of_offBoundary`: the line VSM meets its
  Routh conditions or violates them strictly;
  `LineCascade.mem_den_lyapunovStable_iff_of_offBoundary`, in addition `I_s ≠ 0`): each holds
  iff balanced, Routh and `b < 0`, i.e. iff local exponential stability.

* **Exact decisions on the line-VSM Routh boundary** (the drive–node laws of
  `theorem/Dynamics/CascadeNode.lean`: near a stable DC pole the node contracts,
  `(V − V*) V̇ ≤ (2b/3)(V − V*)² + L |V − V*| ‖π y − π x‖`):
  `LineCascade.mem_den_locallyAsymptoticallyStable_iff_vsm` (within regular parameters: locally
  asymptotically stable iff balanced, the AC part is a locally asymptotically stable member of
  `Line.VSM.family`, and `I_s/(C V*) < 0`) and `LineCascade.mem_den_lyapunovStable_iff_vsm` (the
  same for Lyapunov stability, for `I_s ≠ 0`). With the complete membership of the line VSM
  (`Line.VSM.mem_den_locallyAsymptoticallyStable_iff`,
  `theorem/GridTiedConverter/GFM/HopfLineMembership.lean`: off its degenerate set, balanced and
  strict Routh or on the Hopf boundary with `𝔅_δ > 0`) the cascade is decided at every physical
  model except where the line VSM itself is not (`Line.VSM.Model.Degenerate`): the fold points
  `K(δ*) = 0` with `a₁ = 0` (Bogdanov–Takens) or `a₃ a₂ = a₁` (zero–Hopf) — the other fold
  points are unstable (`Line.VSM.mem_den_unstable_of_fold_of_ne`) — and the Bautin-type points
  `𝔅_δ = 0` of the Hopf boundary.

* **A constant-power source, `I_s = 0`** (the DC voltage is a line of equilibria, the node does
  not contract; it integrates the power mismatch, `C V V̇ = P(x*) − P(y)`):
  `LineCascade.mem_den_lyapunovStable_of_Is_eq_zero` (regular, balanced, line-VSM Routh: Lyapunov
  stable, by the drive–node law `Dynamics.lyapunovStable_cascade_of_exponential` — the AC part is
  locally exponentially stable and `|V − V*| = O(‖x₀ − x*‖)`; never locally asymptotically stable)
  and the exact decision off the line-VSM Routh boundary,
  `LineCascade.mem_den_lyapunovStable_iff_of_offBoundary_of_Is_eq_zero` (Lyapunov stable iff
  balanced and Routh).

Not decided here: Lyapunov stability for `I_s = 0` on the line-VSM Routh boundary. There the AC
part is at best asymptotically, not exponentially, stable (Hopf points with `𝔅_δ > 0`), the drive
error need not be integrable in time, and the DC voltage moves by
`∫ (P(x*) − P(y(t))) dt/(C V)`: deciding it needs the averaged drift of `P` along the slowly
decaying critical oscillation (its mean quadratic part on the centre manifold), which the library
does not state.
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter
open powerlib.Dynamics (State)

namespace DynamicLine

variable (g : DynamicLine)

/-- The five-state field is `C¹` on `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem field_contDiffOn (r : ℝ) :
    ContDiffOn ℝ 1 (g.field r) (nonzeroDC 4) := by
  rw [contDiffOn_euclidean]
  intro i
  have hP : ContDiff ℝ 1 (fun y : State 5 => g.power (y 0) (y 2) (y 3)) := by
    simp only [Line.Network.power_eq]
    fun_prop
  fin_cases i
  · simpa [field] using (Dynamics.contDiff_coord (n := 5) (k := 1) 1).contDiffOn
  · apply ContDiff.contDiffOn
    simp only [field, Fin.mk_one, PiLp.toLp_apply, Matrix.cons_val_one]
    exact ((contDiff_const.sub hP).sub (contDiff_const.mul
      (Dynamics.contDiff_coord (n := 5) (k := 1) 1))).div_const _
  · apply ContDiff.contDiffOn
    simp only [field, Line.Network.rateD]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    fun_prop
  · apply ContDiff.contDiffOn
    simp only [field, Line.Network.rateQ]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    fun_prop
  · simp only [field, Fin.reduceFinMk, PiLp.toLp_apply, Matrix.cons_val, Fin.isValue]
    exact GFL.DCLink.contDiffOn_nodeRate g.C contDiffOn_const
      (contDiff_const.sub hP).contDiffOn
      (Dynamics.contDiff_coord (n := 5) (k := 1) 4).contDiffOn fun y hy => hy

end DynamicLine

namespace LineCascade

/-- A VSM–DC converter on the dynamic line read about a selected angle `δ*` and DC voltage `V*`:
the operating point is `(δ*, 0, i_s(δ*), V*)`. -/
structure Model where
  /-- The parameters. -/
  g : DynamicLine
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected DC voltage `V*`. -/
  V : ℝ

/-- The operating point `(δ*, 0, i_s(δ*), V*)`. -/
def Model.point (m : Model) : State 5 := m.g.point m.δ m.V

/-- The field at the power reference `P_ref`, translated so that the operating point is the
origin. -/
def Model.field (m : Model) (z : State 5) : State 5 := m.g.field m.g.Pref (z + m.point)

/-- The AC part read as a line-VSM model at the same angle. -/
def Model.toVSM (m : Model) : Line.VSM.Model := ⟨m.g.toVSM, m.δ⟩

/-- The DC-node pole `b = I_s/(C V*)` at a balanced point. -/
def Model.b (m : Model) : ℝ := m.g.Is / (m.g.C * m.V)

/-- Power balance: `P(δ*) = P_ref` and `P_s + I_s V* = P(δ*)`. -/
def Model.Balanced (m : Model) : Prop :=
  m.g.qssPower m.δ = m.g.Pref ∧ m.g.Ps + m.g.Is * m.V = m.g.qssPower m.δ

/-- Regular parameters: `V* ≠ 0`, `M, L, C ≠ 0` and `|Z|² > 0`. -/
def Model.Regular (m : Model) : Prop :=
  m.V ≠ 0 ∧ m.g.M ≠ 0 ∧ m.g.L ≠ 0 ∧ m.g.C ≠ 0 ∧ 0 < m.g.absSq

/-- Stability condition: regular, balanced, the line-VSM Routh conditions and `b < 0`. -/
def Model.Stable (m : Model) : Prop :=
  m.Regular ∧ m.Balanced ∧ m.toVSM.Routh ∧ m.b < 0

/-- Instability condition: regular, balanced, and a strict line-VSM Routh violation or
`b > 0`. -/
def Model.Unstable (m : Model) : Prop :=
  m.Regular ∧ m.Balanced ∧ (m.toVSM.RouthViolation ∨ 0 < m.b)

/-- The cascade family: the line VSM feeding its DC link. -/
def family : Family Model Spectral.Requirement 5 0 :=
  Spectral.localFamily Model.field Model.Stable Model.Unstable

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (m.g.field m.g.Pref) m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.g.field m.g.Pref)
    (pt := Model.point) (Spectral.localFamily_isAutonomous _ _ _)

@[tmio M, powerlib_domain] private theorem point_mem (m : Model) (hV : m.V ≠ 0) :
    m.point ∈ nonzeroDC (4 : Fin 5) := by
  simpa [Model.point, DynamicLine.point, nonzeroDC] using hV

@[tmio M, powerlib_domain] private theorem fderiv_point (m : Model) (hV : m.V ≠ 0) :
    fderiv ℝ (m.g.field m.g.Pref) m.point =
      Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (m.g.model m.δ m.V).A :=
  m.g.fderiv_point m.g.Pref hV

/-- Within regular parameters the operating point is an equilibrium iff it is balanced. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.field_point_eq_zero_iff (m : Model) (h : m.Regular) :
    m.g.field m.g.Pref m.point = 0 ↔ m.Balanced := by
  obtain ⟨hV, hM, hL, hC, hZ⟩ := h
  rw [Model.point, m.g.field_point_eq_zero_iff hL hZ,
    m.g.toPlant.openField_eq_zero_iff hM hC hV, m.g.toPlant_Pe hZ]
  simp only [Dynamics.mk3_zero, Dynamics.mk3_one, Dynamics.mk3_two, true_and, Model.Balanced,
    Plant.Psrc]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩

/-- **The cascade spectrum**: at a balanced point (`V* ≠ 0`) the characteristic polynomial is
that of the line VSM times the DC-node factor, `det(sI − J) = det(sI − J_VSM)(s − b)`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix (m : Model) (hV : m.V ≠ 0)
    (hb : m.Balanced) (s : ℂ) :
    (Linear.characteristicMatrix (m.g.model m.δ m.V).A s).det =
      (Linear.characteristicMatrix m.toVSM.jac s).det * (s + ((-m.b : ℝ) : ℂ)) := by
  have hj : m.g.dcPole m.δ m.V = m.b := m.g.dcPole_of_balance hV hb.2
  rw [show (m.g.model m.δ m.V).A = m.g.jacobian m.δ (m.g.is m.δ).re (m.g.is m.δ).im m.V from rfl,
    m.g.det_characteristicMatrix_jacobian]
  rw [DynamicLine.dcPole] at hj
  change _ * (s - ((m.g.nodeSlope (m.g.qssPower m.δ) m.V : ℝ) : ℂ)) =
    (Linear.characteristicMatrix (m.g.toVSM.jacobian m.δ (m.g.is m.δ).re (m.g.is m.δ).im) s).det *
      _
  rw [hj]
  push_cast
  ring

/-- At a balanced point the Jacobian is Hurwitz iff the line VSM meets its quartic Routh
conditions and the DC-node pole is stable, `b < 0`. Static evidence on the model. -/
@[tmio TM, powerlib_domain] theorem Model.isHurwitz_iff (m : Model) (hV : m.V ≠ 0)
    (hb : m.Balanced) :
    LinearSystems.IsHurwitz (m.g.model m.δ m.V).A ↔ m.toVSM.Routh ∧ m.b < 0 := by
  rw [← Linear.spectrallyStable_iff_isHurwitz,
    Linear.spectrallyStable_iff_of_extra_pole (m.det_characteristicMatrix hV hb),
    Linear.spectrallyStable_iff_isHurwitz,
    Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
      m.toVSM.det_characteristicMatrix, neg_pos]
  rfl

/-- A strict line-VSM Routh violation or `b > 0` gives a Jacobian eigenvalue with positive real
part. -/
@[tmio M, powerlib_domain] private theorem exists_eigenpair_of_unstable (m : Model)
    (hV : m.V ≠ 0) (hb : m.Balanced) (h : m.toVSM.RouthViolation ∨ 0 < m.b) :
    ∃ (μ : ℂ) (v : Fin 5 → ℂ),
      v ≠ 0 ∧ (m.g.model m.δ m.V).A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨s, hs, hre⟩ := Linear.exists_root_re_pos_of_extra_pole
    (m.det_characteristicMatrix hV hb) (by
      rcases h with h | h
      · obtain ⟨s, hs, hre⟩ := Criteria.exists_quartic_root_re_pos_of_violation h
        exact Or.inl ⟨s, by rw [m.toVSM.det_characteristicMatrix]; exact hs, hre⟩
      · exact Or.inr (neg_neg_of_pos h))
  exact Criteria.exists_eigenpair_re_pos_of_characteristic_root _ hs hre

/-- **Local exponential stability.** A regular balanced point whose line VSM meets its quartic
Routh conditions, with a stable DC-node pole `b < 0`, is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (h : m.Stable) : connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨hr, hb, hR, hneg⟩ := h
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_nonzeroDC 4)
    (point_mem m hr.1) _ (m.g.field_contDiffOn _) ((m.field_point_eq_zero_iff hr).mpr hb)
    (fderiv_point m hr.1) ((m.isHurwitz_iff hr.1 hb).mpr ⟨hR, hneg⟩)

/-- **Instability.** A regular balanced point with a strict line-VSM Routh violation, or with an
unstable DC-node pole `b > 0`, is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (h : m.Unstable) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨hr, hb, hu⟩ := h
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_nonzeroDC 4)
    (point_mem m hr.1) _ (m.g.field_contDiffOn _) ((m.field_point_eq_zero_iff hr).mpr hb)
    (fderiv_point m hr.1) (exists_eigenpair_of_unstable m hr.1 hb hu)

/-- Soundness of every translation of the cascade family. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => ?_) (fun m h => ?_)
  · exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (mem_den_flow_iff.mp (mem_den_locallyExponentiallyStable m h))
  · exact (Flow.Property.holds_shift_iff .unstable).mpr
      (mem_den_flow_iff.mp (mem_den_unstable m h))

/-- **Exact local exponential stability of the cascade.** Within regular parameters, the
operating point is locally exponentially stable iff it is balanced, the line VSM meets its quartic
Routh conditions and the DC-node pole is stable, `I_s/(C V*) < 0` (converse linearization for the
field `C¹` on `V ≠ 0`, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (h : m.Regular) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.Balanced ∧ m.toVSM.Routh ∧ m.b < 0) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  change LocallyExponentiallyStable _ _ ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local (isOpen_nonzeroDC 4)
    (point_mem m h.1) _ (m.g.field_contDiffOn _) (fderiv_point m h.1),
    m.field_point_eq_zero_iff h]
  constructor
  · rintro ⟨hb, hH⟩
    exact ⟨hb, (m.isHurwitz_iff h.1 hb).mp hH⟩
  · rintro ⟨hb, hR⟩
    exact ⟨hb, (m.isHurwitz_iff h.1 hb).mpr hR⟩

/-- Within regular parameters the local exponential translation is exact: the generated space of
the stability condition is the locally exponentially stable regular models. -/
@[tmio TM, powerlib_domain] theorem realize_eq_den_inter :
    connection% (TMIO.realize family.meets (family.translate (.flow .locallyExponentiallyStable)) =
      family.den (.flow .locallyExponentiallyStable) ∩ {m : Model | m.Regular}) :=
  Spectral.local_realize_eq_den_inter_of_iff (Or.inr (Or.inr rfl)) (fun m h => h.1)
    fun m hr => by
      have h := mem_den_locallyExponentiallyStable_iff m hr
      unfold TMIO.Statement at h
      show m.Stable ↔ m ∈ family.den (.flow .locallyExponentiallyStable)
      rw [h]
      exact ⟨fun ⟨_, hb, hR, hneg⟩ => ⟨hb, hR, hneg⟩, fun ⟨hb, hR, hneg⟩ => ⟨hr, hb, hR, hneg⟩⟩

/-- The line-VSM Routh conditions are its local exponential stability (within a physical network,
`M, D > 0`, at a balanced angle; `Line.VSM.mem_den_locallyExponentiallyStable` and
`Line.VSM.exactUnder_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] private theorem routh_iff_vsm (m : Model) (hN : m.g.Physical)
    (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hb : m.g.qssPower m.δ = m.g.Pref) :
    m.toVSM.Routh ↔ m.toVSM ∈ Line.VSM.family.den (.flow .locallyExponentiallyStable) := by
  have hp : Line.VSM.Meets m.toVSM .physical := ⟨hN, hM, hD⟩
  constructor
  · intro hR
    have h := Line.VSM.mem_den_locallyExponentiallyStable m.toVSM hp hb hR
    unfold TMIO.Statement at h
    exact h
  · intro hs
    have hex := Line.VSM.exactUnder_locallyExponentiallyStable
    unfold TMIO.Statement at hex
    have hm := (Spectral.exactUnder_iff_forall.mp hex m.toVSM
      ((TMIO.mem_realize _ _ _).mpr fun q hq => by
        rw [Set.mem_singleton_iff.mp hq]; exact hp)).mpr hs
    exact (TMIO.mem_realize _ _ _).mp hm .routh
      (by simp [Line.VSM.family, Line.VSM.translate, Spectral.table])

/-- **The cascade decision read through the line-VSM family.** For a physical network, `M, D > 0`,
`C, V* ≠ 0`: the cascade is locally exponentially stable iff it is balanced, its AC part
(`Model.toVSM`) is a locally exponentially stable member of `Line.VSM.family` (whose boundary is
the explicit cubic inequality of `Line.VSM.mem_den_locallyExponentiallyStable_iff`) and
`I_s/(C V*) < 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_vsm (m : Model)
    (hN : m.g.Physical) (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hC : m.g.C ≠ 0) (hV : m.V ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.Balanced ∧ m.toVSM ∈ Line.VSM.family.den (.flow .locallyExponentiallyStable) ∧
        m.b < 0) := by
  have hr : m.Regular := ⟨hV, hM.ne', hN.L.ne', hC, hN.absSq_pos⟩
  have h := mem_den_locallyExponentiallyStable_iff m hr
  unfold TMIO.Statement at h ⊢
  rw [h]
  constructor
  · rintro ⟨hb, hR, hneg⟩
    exact ⟨hb, (routh_iff_vsm m hN hM hD hb.1).mp hR, hneg⟩
  · rintro ⟨hb, hs, hneg⟩
    exact ⟨hb, (routh_iff_vsm m hN hM hD hb.1).mpr hs, hneg⟩

/-- **An exporting constant-current source is unstable** (the GFM analogue of the GFL inverter
mode, `GFL.DCLink.Cascade.mem_den_unstable_of_inverter`). With `P_s = 0`, `C, V* > 0` and regular
parameters, a balanced point exporting power, `P(δ*) > 0`, has the DC-node pole
`b = P(δ*)/(C V*²) > 0`: unstable, whatever the line-VSM gains. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_export (m : Model) (h : m.Regular)
    (hb : m.Balanced) (hPs : m.g.Ps = 0) (hC : 0 < m.g.C) (hV : 0 < m.V)
    (hP : 0 < m.g.qssPower m.δ) : connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m ⟨h, hb, Or.inr ?_⟩
  have hI : 0 < m.g.Is := by
    have h2 := hb.2
    rw [hPs, zero_add] at h2
    rw [← h2] at hP
    exact pos_of_mul_pos_left hP hV.le
  exact div_pos hI (mul_pos hC hV)

/-- **Necessity, boundaries included.** Within regular parameters a Lyapunov stable operating
point is balanced, its line VSM does not violate its quartic Routh conditions strictly, and
`b ≤ 0` (otherwise it is an equilibrium with a right-half-plane eigenvalue, or not an
equilibrium). -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_lyapunovStable (m : Model)
    (h : m.Regular) (hs : m ∈ family.den (.flow .lyapunovStable)) :
    m.Balanced ∧ ¬ m.toVSM.RouthViolation ∧ m.b ≤ 0 := by
  have heq : m.g.field m.g.Pref m.point = 0 :=
    Dynamics.isEquilibrium_of_lyapunovStable_local (isOpen_nonzeroDC 4) (point_mem m h.1)
      (m.g.field_contDiffOn _) (mem_den_flow_iff.mp hs)
  have hb := (m.field_point_eq_zero_iff h).mp heq
  have hnot : ¬ (m.toVSM.RouthViolation ∨ 0 < m.b) := fun hu => by
    have hun := mem_den_unstable m ⟨h, hb, hu⟩
    unfold TMIO.Statement at hun
    have hn := Spectral.not_mem_den_lyapunovStable_of_unstable hun
    unfold TMIO.Statement at hn
    exact hn hs
  push Not at hnot
  exact ⟨hb, hnot.1, hnot.2⟩

/-- **A constant-power source gives a line of equilibria.** At a regular balanced point with
`I_s = 0`, every `(δ*, 0, i_s(δ*), V)` with `V` of the sign of `V*` is an equilibrium (the node
power `P_s − P(δ*)` vanishes): not locally asymptotically stable. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_Is_eq_zero
    (m : Model) (h : m.Regular) (hb : m.Balanced) (hI : m.g.Is = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  change ¬ LocalAsymptoticStable _ _
  have heq := (m.field_point_eq_zero_iff h).mpr hb
  refine Dynamics.not_localAsymptoticStable_of_line (v := m.V • EuclideanSpace.single 4 1)
    (by simpa using h.1) fun t ht => ?_
  have hPs : m.g.Ps = m.g.qssPower m.δ := by simpa [hI] using hb.2
  ext i
  have h0 := congrArg (fun y : State 5 => y i) heq
  fin_cases i <;>
    simp [DynamicLine.field, Model.point, DynamicLine.point, GFL.DCLink.nodeRate, hI] at h0 ⊢ <;>
      first | exact h0 | simp [hPs, Line.Network.qssPower]

/-- **Necessity for local asymptotic stability.** Within regular parameters a locally
asymptotically stable operating point is balanced, its line VSM does not violate its quartic
Routh conditions strictly, and the DC-node pole is stable, `b < 0`. -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_locallyAsymptoticallyStable
    (m : Model) (h : m.Regular) (hs : m ∈ family.den (.flow .locallyAsymptoticallyStable)) :
    m.Balanced ∧ ¬ m.toVSM.RouthViolation ∧ m.b < 0 := by
  obtain ⟨hb, hv, hle⟩ :=
    closedRouth_of_mem_den_lyapunovStable m h (Spectral.den_las_subset_lyapunovStable hs)
  refine ⟨hb, hv, lt_of_le_of_ne hle fun h0 => ?_⟩
  have hI : m.g.Is = 0 := by
    rw [Model.b, div_eq_zero_iff] at h0
    exact h0.resolve_right (mul_ne_zero h.2.2.2.1 h.1)
  have hn := not_mem_den_locallyAsymptoticallyStable_of_Is_eq_zero m h hb hI
  unfold TMIO.Statement at hn
  exact hn hs

/-- **Local asymptotic stability off the line-VSM Routh boundary.** Within regular parameters,
when the line VSM meets its quartic Routh conditions or violates them strictly, the operating
point is locally asymptotically stable iff it is balanced, Routh and `b < 0` (iff locally
exponentially stable). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_offBoundary
    (m : Model) (h : m.Regular) (hoff : m.toVSM.Routh ∨ m.toVSM.RouthViolation) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m.Balanced ∧ m.toVSM.Routh ∧ m.b < 0) := by
  unfold TMIO.Statement
  constructor
  · intro hs
    obtain ⟨hb, hv, hneg⟩ := closedRouth_of_mem_den_locallyAsymptoticallyStable m h hs
    exact ⟨hb, hoff.resolve_right hv, hneg⟩
  · intro hc
    have hl := (mem_den_locallyExponentiallyStable_iff m h).mpr hc
    exact Spectral.den_locallyExponentiallyStable_subset_las hl

/-- **Lyapunov stability off the boundaries.** Within regular parameters, when the line VSM meets
its quartic Routh conditions or violates them strictly and `I_s ≠ 0`, the operating point is
Lyapunov stable iff it is balanced, Routh and `b < 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_offBoundary (m : Model)
    (h : m.Regular) (hoff : m.toVSM.Routh ∨ m.toVSM.RouthViolation) (hI : m.g.Is ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m.Balanced ∧ m.toVSM.Routh ∧ m.b < 0) := by
  unfold TMIO.Statement
  constructor
  · intro hs
    obtain ⟨hb, hv, hle⟩ := closedRouth_of_mem_den_lyapunovStable m h hs
    refine ⟨hb, hoff.resolve_right hv, lt_of_le_of_ne hle fun h0 => hI ?_⟩
    rw [Model.b, div_eq_zero_iff] at h0
    exact h0.resolve_right (mul_ne_zero h.2.2.2.1 h.1)
  · intro hc
    have hl := (mem_den_locallyExponentiallyStable_iff m h).mpr hc
    exact Spectral.den_locallyExponentiallyStable_subset_lyapunovStable hl

/-! ## The cascade decision on the line-VSM boundary -/

@[tmio TM, powerlib_domain] private theorem vsm_mem_den_flow_iff {m : Line.VSM.Model}
    {P : Flow.Property} : m ∈ Line.VSM.family.den (.flow P) ↔ P.holds m.g.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Line.VSM.Model => m.g.field)
    (pt := Line.VSM.Model.point) Line.VSM.family_isAutonomous

@[tmio M, powerlib_domain] private theorem proj54_point (m : Model) :
    Dynamics.proj54 m.point = m.toVSM.point := by
  ext i
  fin_cases i <;> simp [Dynamics.proj54, Model.point, DynamicLine.point, Model.toVSM,
    Line.VSM.Model.point, Line.VSM.qss]

/-- The AC rows of the cascade are the line-VSM field: the drive does not read `V`. -/
@[tmio M, powerlib_domain] private theorem proj54_field (m : Model) (y : State 5) :
    Dynamics.proj54 (m.g.field m.g.Pref y) = m.toVSM.g.field (Dynamics.proj54 y) := by
  ext i
  fin_cases i <;> simp [Dynamics.proj54, DynamicLine.field, Model.toVSM, Line.VSM.field]

/-- **The DC node contracts near a stable DC pole.** At a regular balanced point with `b < 0`,
near the operating point `(V − V*) V̇ ≤ (2b/3)(V − V*)² + L |V − V*| ‖π y − π x‖`, `π` the AC
coordinates: `C V V̇ = I_s (V − V*) + P(x*) − P(y)` with `P` Lipschitz near the operating point and
`V/V* ∈ (1/2, 3/2)`. -/
@[tmio M, powerlib_domain] private theorem exists_node_estimate (m : Model) (h : m.Regular)
    (hb : m.Balanced) (hneg : m.b < 0) :
    ∃ ρ c L : ℝ, 0 < ρ ∧ 0 < c ∧ 0 ≤ L ∧ ∀ y : State 5, ‖y - m.point‖ < ρ →
      inner ℝ ((y - m.point) - Dynamics.incl45 (Dynamics.proj54 (y - m.point)))
        (m.g.field m.g.Pref y - Dynamics.incl45 (Dynamics.proj54 (m.g.field m.g.Pref y))) ≤
      -c * ‖(y - m.point) - Dynamics.incl45 (Dynamics.proj54 (y - m.point))‖ ^ 2 +
        L * ‖(y - m.point) - Dynamics.incl45 (Dynamics.proj54 (y - m.point))‖ *
          ‖Dynamics.proj54 y - Dynamics.proj54 m.point‖ := by
  obtain ⟨hV, -, -, hC, -⟩ := h
  set Pv : State 4 → ℝ := fun v => m.g.power (v 0) (v 2) (v 3) with hPv
  have hPc : ContDiff ℝ 1 Pv := by
    simp only [hPv, Line.Network.power_eq]
    fun_prop
  obtain ⟨K, t, ht, hK⟩ := (hPc.contDiffAt (x := Dynamics.proj54 m.point)).exists_lipschitzOnWith
  obtain ⟨ρP, hρP, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hVa : 0 < |m.V| := abs_pos.mpr hV
  have hCV : 0 < |m.g.C * m.V| := abs_pos.mpr (mul_ne_zero hC hV)
  refine ⟨min (|m.V| / 2) ρP, -(2 / 3 * m.b), 2 * K / |m.g.C * m.V|, by positivity,
    by linarith, by positivity, fun y hy => ?_⟩
  rw [Dynamics.inner_sub_incl45_proj54, Dynamics.norm_sub_incl45_proj54]
  have hy4 : (y - m.point) 4 = y 4 - m.V := by simp [Model.point, DynamicLine.point]
  have hf4 : m.g.field m.g.Pref y 4 =
      GFL.DCLink.nodeRate m.g.C m.g.Is (m.g.Ps - m.g.power (y 0) (y 2) (y 3)) (y 4) := by
    simp [DynamicLine.field]
  rw [hy4, hf4]
  set a := y 4 - m.V with ha
  have hab : |a| < |m.V| / 2 := by
    have := (Dynamics.abs_coord_sub_le m.point y 4).trans_lt (hy.trans_le (min_le_left _ _))
    simpa [Model.point, DynamicLine.point, ha] using this
  -- the drive distance controls the power
  have hmem : ∀ z, ‖z - Dynamics.proj54 m.point‖ < ρP → z ∈ t := fun z hz =>
    hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hz)
  have hyP : ‖Dynamics.proj54 y - Dynamics.proj54 m.point‖ < ρP := by
    rw [← map_sub]
    exact (Dynamics.norm_proj54_le _).trans_lt (hy.trans_le (min_le_right _ _))
  have hdP := hK.dist_le_mul (Dynamics.proj54 y) (hmem _ hyP) (Dynamics.proj54 m.point)
    (hmem _ (by rw [sub_self, norm_zero]; exact hρP))
  rw [Real.dist_eq, dist_eq_norm] at hdP
  have hPy : Pv (Dynamics.proj54 y) = m.g.power (y 0) (y 2) (y 3) := by
    simp [hPv, Dynamics.proj54]
  have hPx : Pv (Dynamics.proj54 m.point) = m.g.Ps + m.g.Is * m.V := by
    rw [hb.2]
    simp [hPv, Dynamics.proj54, Model.point, DynamicLine.point, Line.Network.qssPower]
  rw [hPy, hPx] at hdP
  set d := ‖Dynamics.proj54 y - Dynamics.proj54 m.point‖ with hd
  set E := m.g.power (y 0) (y 2) (y 3) with hE
  set N := m.g.Ps + m.g.Is * m.V - E with hN
  have hNd : |N| ≤ K * d := by rw [hN, abs_sub_comm]; exact hdP
  have hVy : y 4 = m.V + a := by rw [ha]; ring
  have ha2 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have hVV : m.V ^ 2 = |m.V| ^ 2 := (sq_abs _).symm
  have haV : |a * m.V| < |m.V| ^ 2 / 2 := by
    rw [abs_mul]
    nlinarith
  have hnum : 0 < (m.V - 2 * a) * y 4 := by
    rw [hVy]
    have h1 := le_abs_self (a * m.V)
    have h4 : |a| ^ 2 < (|m.V| / 2) ^ 2 := by
      have := abs_nonneg a
      nlinarith
    nlinarith
  have hVyV : 0 < y 4 * m.V := by
    rw [hVy]
    have h1 := neg_abs_le (a * m.V)
    nlinarith
  have hy4ne : y 4 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hVyV; exact lt_irrefl _ hVyV
  have hrate : a * GFL.DCLink.nodeRate m.g.C m.g.Is (m.g.Ps - E) (y 4) =
      m.b * (m.V / y 4) * a ^ 2 + a * N / (m.g.C * y 4) := by
    rw [GFL.DCLink.nodeRate, Model.b, hN]
    field_simp
    rw [hVy]
    ring
  rw [hrate]
  -- the contraction term: `V*/V ≥ 2/3`
  have ht : 2 / 3 ≤ m.V / y 4 := by
    have e : m.V / y 4 - 2 / 3 = (m.V - 2 * a) * y 4 / (3 * y 4 ^ 2) := by
      field_simp
      rw [hVy]
      ring
    have : 0 ≤ m.V / y 4 - 2 / 3 := by rw [e]; positivity
    linarith
  have h1 : m.b * (m.V / y 4) * a ^ 2 ≤ 2 / 3 * m.b * |a| ^ 2 := by
    rw [ha2]
    have := mul_le_mul_of_nonpos_left ht hneg.le
    nlinarith [sq_nonneg |a|]
  -- the coupling term: `|C V| ≥ |C V*|/2`
  have hy4 : |m.V| / 2 ≤ |y 4| := by
    rw [hVy]
    have := abs_add_le (m.V + a) (-a)
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  have hCy : |m.g.C * m.V| / 2 ≤ |m.g.C * y 4| := by
    rw [abs_mul, abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hy4 (abs_nonneg _)
  have hCy0 : 0 < |m.g.C * m.V| / 2 := by positivity
  have h2 : a * N / (m.g.C * y 4) ≤ 2 * K / |m.g.C * m.V| * |a| * d := by
    calc a * N / (m.g.C * y 4) ≤ |a * N / (m.g.C * y 4)| := le_abs_self _
      _ = |a| * |N| / |m.g.C * y 4| := by rw [abs_div, abs_mul]
      _ ≤ |a| * |N| / (|m.g.C * m.V| / 2) :=
          div_le_div_of_nonneg_left (by positivity) hCy0 hCy
      _ ≤ |a| * (K * d) / (|m.g.C * m.V| / 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNd (abs_nonneg _)) hCy0.le
      _ = 2 * K / |m.g.C * m.V| * |a| * d := by field_simp
  have e : -(-(2 / 3 * m.b)) * |a| ^ 2 = 2 / 3 * m.b * |a| ^ 2 := by ring
  rw [e]
  exact add_le_add h1 h2

/-- **Exact local asymptotic stability of the cascade, boundary included.** Within regular
parameters the operating point is locally asymptotically stable iff it is balanced, its AC part
is a locally asymptotically stable member of `Line.VSM.family`, and the DC-node pole is stable,
`I_s/(C V*) < 0`. `⇐`: the drive–node law `Dynamics.localAsymptoticStable_cascade` (the DC node
contracts, `exists_node_estimate`); `⇒`: balance and `b < 0` are necessary
(`closedRouth_of_mem_den_locallyAsymptoticallyStable`) and the drive of a locally asymptotically
stable cascade is locally asymptotically stable
(`Dynamics.localAsymptoticStable_drive_of_cascade`). This holds on the line-VSM Routh boundary
as well: the cascade is decided wherever the line VSM is
(`Line.VSM.mem_den_locallyAsymptoticallyStable_iff`,
`theorem/GridTiedConverter/GFM/HopfLineMembership.lean`, decides every physical model off its
fold `K = 0` and its Bautin-type points `𝔅_δ = 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_vsm (m : Model)
    (h : m.Regular) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m.Balanced ∧ m.toVSM ∈ Line.VSM.family.den (.flow .locallyAsymptoticallyStable) ∧
        m.b < 0) := by
  unfold TMIO.Statement
  constructor
  · intro hs
    obtain ⟨hb, -, hneg⟩ := closedRouth_of_mem_den_locallyAsymptoticallyStable m h hs
    refine ⟨hb, ?_, hneg⟩
    rw [vsm_mem_den_flow_iff]
    have hf := mem_den_flow_iff.mp hs
    change LocalAsymptoticStable _ _ at hf
    change LocalAsymptoticStable _ _
    rw [← proj54_point]
    exact Dynamics.localAsymptoticStable_drive_of_cascade Dynamics.proj54_incl45
      Dynamics.norm_incl45 Dynamics.norm_proj54_le (proj54_field m) (isOpen_nonzeroDC 4)
      (point_mem m h.1) (m.g.field_contDiffOn _) m.toVSM.g.contDiff_field.contDiffAt hf
  · rintro ⟨hb, hvsm, hneg⟩
    rw [mem_den_flow_iff]
    rw [vsm_mem_den_flow_iff] at hvsm
    change LocalAsymptoticStable _ _ at hvsm
    change LocalAsymptoticStable _ _
    obtain ⟨ρ, c, L, hρ, hc, hL, hnode⟩ := exists_node_estimate m h hb hneg
    rw [← proj54_point] at hvsm
    exact Dynamics.localAsymptoticStable_cascade Dynamics.norm_incl45 Dynamics.norm_proj54_le
      Dynamics.norm_sub_incl45_proj54_le (proj54_field m) hρ hc hL hnode hvsm

/-- **Exact Lyapunov stability of the cascade, boundary included** (a source current `I_s ≠ 0`):
within regular parameters the operating point is Lyapunov stable iff it is balanced, its AC part
is a Lyapunov stable member of `Line.VSM.family`, and `I_s/(C V*) < 0`
(`Dynamics.lyapunovStable_cascade`, `Dynamics.lyapunovStable_drive_of_cascade`). For `I_s = 0` the
DC voltage is a line of equilibria and the node does not contract: that case is decided off the
line-VSM Routh boundary by `mem_den_lyapunovStable_iff_of_offBoundary_of_Is_eq_zero`. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_vsm (m : Model) (h : m.Regular)
    (hI : m.g.Is ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m.Balanced ∧ m.toVSM ∈ Line.VSM.family.den (.flow .lyapunovStable) ∧ m.b < 0) := by
  unfold TMIO.Statement
  constructor
  · intro hs
    obtain ⟨hb, -, hle⟩ := closedRouth_of_mem_den_lyapunovStable m h hs
    have hneg : m.b < 0 := lt_of_le_of_ne hle fun h0 => hI (by
      rw [Model.b, div_eq_zero_iff] at h0
      exact h0.resolve_right (mul_ne_zero h.2.2.2.1 h.1))
    refine ⟨hb, ?_, hneg⟩
    rw [vsm_mem_den_flow_iff]
    have hf := mem_den_flow_iff.mp hs
    change LyapunovStable _ _ at hf
    change LyapunovStable _ _
    rw [← proj54_point]
    exact Dynamics.lyapunovStable_drive_of_cascade Dynamics.proj54_incl45 Dynamics.norm_incl45
      Dynamics.norm_proj54_le (proj54_field m) (isOpen_nonzeroDC 4) (point_mem m h.1)
      (m.g.field_contDiffOn _) m.toVSM.g.contDiff_field.contDiffAt hf
  · rintro ⟨hb, hvsm, hneg⟩
    rw [mem_den_flow_iff]
    rw [vsm_mem_den_flow_iff] at hvsm
    change LyapunovStable _ _ at hvsm
    change LyapunovStable _ _
    obtain ⟨ρ, c, L, hρ, hc, hL, hnode⟩ := exists_node_estimate m h hb hneg
    rw [← proj54_point] at hvsm
    exact Dynamics.lyapunovStable_cascade Dynamics.norm_incl45 Dynamics.norm_proj54_le
      Dynamics.norm_sub_incl45_proj54_le (proj54_field m) hρ hc hL hnode hvsm

/-! ## A constant-power source: the DC voltage integrates the power mismatch -/

/-- **The DC node is slaved to the drive for a constant-power source.** At a regular balanced
point with `I_s = 0`, near the operating point `|V̇| ≤ L ‖π y − π x‖`, `π` the AC coordinates:
`C V V̇ = P(x*) − P(y)` with `P` Lipschitz near the operating point and `|V| ≥ |V*|/2`. -/
@[tmio M, powerlib_domain] private theorem exists_node_bound (m : Model) (h : m.Regular)
    (hb : m.Balanced) (hI : m.g.Is = 0) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ ∀ y : State 5, ‖y - m.point‖ < ρ →
      ‖m.g.field m.g.Pref y - Dynamics.incl45 (Dynamics.proj54 (m.g.field m.g.Pref y))‖ ≤
        L * ‖Dynamics.proj54 y - Dynamics.proj54 m.point‖ := by
  obtain ⟨hV, -, -, hC, -⟩ := h
  set Pv : State 4 → ℝ := fun v => m.g.power (v 0) (v 2) (v 3) with hPv
  have hPc : ContDiff ℝ 1 Pv := by
    simp only [hPv, Line.Network.power_eq]
    fun_prop
  obtain ⟨K, t, ht, hK⟩ := (hPc.contDiffAt (x := Dynamics.proj54 m.point)).exists_lipschitzOnWith
  obtain ⟨ρP, hρP, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hVa : 0 < |m.V| := abs_pos.mpr hV
  have hCV : 0 < |m.g.C * m.V| := abs_pos.mpr (mul_ne_zero hC hV)
  refine ⟨min (|m.V| / 2) ρP, 2 * K / |m.g.C * m.V|, by positivity, by positivity,
    fun y hy => ?_⟩
  rw [Dynamics.norm_sub_incl45_proj54]
  have hf4 : m.g.field m.g.Pref y 4 =
      GFL.DCLink.nodeRate m.g.C m.g.Is (m.g.Ps - m.g.power (y 0) (y 2) (y 3)) (y 4) := by
    simp [DynamicLine.field]
  rw [hf4]
  have hab : |y 4 - m.V| < |m.V| / 2 := by
    have := (Dynamics.abs_coord_sub_le m.point y 4).trans_lt (hy.trans_le (min_le_left _ _))
    simpa [Model.point, DynamicLine.point] using this
  have hmem : ∀ z, ‖z - Dynamics.proj54 m.point‖ < ρP → z ∈ t := fun z hz =>
    hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hz)
  have hyP : ‖Dynamics.proj54 y - Dynamics.proj54 m.point‖ < ρP := by
    rw [← map_sub]
    exact (Dynamics.norm_proj54_le _).trans_lt (hy.trans_le (min_le_right _ _))
  have hdP := hK.dist_le_mul (Dynamics.proj54 y) (hmem _ hyP) (Dynamics.proj54 m.point)
    (hmem _ (by rw [sub_self, norm_zero]; exact hρP))
  rw [Real.dist_eq, dist_eq_norm] at hdP
  have hPy : Pv (Dynamics.proj54 y) = m.g.power (y 0) (y 2) (y 3) := by
    simp [hPv, Dynamics.proj54]
  have hPx : Pv (Dynamics.proj54 m.point) = m.g.Ps := by
    have h2 := hb.2
    rw [hI, zero_mul, add_zero] at h2
    rw [h2]
    simp [hPv, Dynamics.proj54, Model.point, DynamicLine.point, Line.Network.qssPower]
  rw [hPy, hPx, abs_sub_comm] at hdP
  set d := ‖Dynamics.proj54 y - Dynamics.proj54 m.point‖ with hd
  set N := m.g.Ps - m.g.power (y 0) (y 2) (y 3) with hN
  have hy4 : |m.V| / 2 ≤ |y 4| := by
    have := abs_add_le (y 4 - m.V) m.V
    rw [sub_add_cancel] at this
    have := abs_sub_abs_le_abs_sub m.V (y 4)
    rw [abs_sub_comm] at this
    linarith
  have hCy : |m.g.C * m.V| / 2 ≤ |m.g.C * y 4| := by
    rw [abs_mul, abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hy4 (abs_nonneg _)
  have hCy0 : 0 < |m.g.C * m.V| / 2 := by positivity
  rw [GFL.DCLink.nodeRate, hI, zero_add]
  calc |N / y 4 / m.g.C| = |N| / |m.g.C * y 4| := by
        rw [abs_div, abs_div, abs_mul, div_div, mul_comm |y 4|]
    _ ≤ |N| / (|m.g.C * m.V| / 2) := div_le_div_of_nonneg_left (abs_nonneg _) hCy0 hCy
    _ ≤ K * d / (|m.g.C * m.V| / 2) := div_le_div_of_nonneg_right hdP hCy0.le
    _ = 2 * K / |m.g.C * m.V| * d := by field_simp

/-- **A constant-power source behind an exponentially stable line VSM is Lyapunov stable.** At a
regular balanced point with `I_s = 0` whose line VSM meets its quartic Routh conditions, the
operating point is Lyapunov stable: the AC part is locally exponentially stable and the DC
voltage, which integrates the power mismatch `P(x*) − P(y)`, moves by `O(‖x₀ − x*‖)`
(`Dynamics.lyapunovStable_cascade_of_exponential`). It is not locally asymptotically stable
(`not_mem_den_locallyAsymptoticallyStable_of_Is_eq_zero`: the DC voltage is a line of
equilibria). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_of_Is_eq_zero (m : Model)
    (h : m.Regular) (hb : m.Balanced) (hI : m.g.Is = 0) (hR : m.toVSM.Routh) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  change LyapunovStable _ _
  have heq := (m.field_point_eq_zero_iff h).mpr hb
  have hdrive0 : m.toVSM.g.field m.toVSM.point = 0 := by
    rw [← proj54_point, ← proj54_field, heq, map_zero]
  have hles : LocallyExponentiallyStable m.toVSM.g.field m.toVSM.point :=
    hurwitz_linearization_locally_exponentially_stable m.toVSM.jac m.toVSM.g.contDiff_field
      hdrive0 m.toVSM.fderiv_point
      ((Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
        m.toVSM.det_characteristicMatrix).mpr hR)
  obtain ⟨ρ, L, hρ, hL, hnode⟩ := exists_node_bound m h hb hI
  rw [← proj54_point] at hles
  exact Dynamics.lyapunovStable_cascade_of_exponential Dynamics.norm_incl45
    Dynamics.norm_proj54_le Dynamics.norm_sub_incl45_proj54_le (proj54_field m) hρ hL hnode hles

/-- **Exact Lyapunov stability for a constant-power source off the line-VSM Routh boundary.**
Within regular parameters, with `I_s = 0` and the line VSM meeting its quartic Routh conditions or
violating them strictly, the operating point is Lyapunov stable iff it is balanced and the line
VSM meets its Routh conditions (`mem_den_lyapunovStable_of_Is_eq_zero`; necessity
`closedRouth_of_mem_den_lyapunovStable`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_offBoundary_of_Is_eq_zero
    (m : Model) (h : m.Regular) (hoff : m.toVSM.Routh ∨ m.toVSM.RouthViolation)
    (hI : m.g.Is = 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔ m.Balanced ∧ m.toVSM.Routh) := by
  unfold TMIO.Statement
  constructor
  · intro hs
    obtain ⟨hb, hv, -⟩ := closedRouth_of_mem_den_lyapunovStable m h hs
    exact ⟨hb, hoff.resolve_right hv⟩
  · rintro ⟨hb, hR⟩
    have hl := mem_den_lyapunovStable_of_Is_eq_zero m h hb hI hR
    unfold TMIO.Statement at hl
    exact hl

end LineCascade

end powerlib.GFM.DCLink
