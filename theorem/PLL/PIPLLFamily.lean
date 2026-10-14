import theorem.PLL.PIPLL
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.LaSalle.Passivity

/-! # The PI-PLL family

Model boundary. A complete system is a PI phase-locked loop with a general phase-detector
characteristic, read about one selected operating point:
* parameters `h : ℝ → ℝ` (phase-detector characteristic, `C¹` on all of `ℝ`), PI gains `K_p`,
  `K_i` (any reals), constant grid-frequency offset `δω` (constant input), and the selected phase
  `θ*`; the selected point is `x* = (θ*, δω / K_i)` (`= (θ*, 0)` when `K_i = 0`);
* state `(θ, η) ∈ ℝ² = EuclideanSpace ℝ (Fin 2)` in this order, field
  `θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)` (`piPLLField`, `theorem/PLL/PIPLL.lean`), continuous
  time, no delay, PWM, saturation, current loop, filter or line dynamics; feedback signs as in
  `PIPLL.lean`;
* the system map reads the model as the autonomous field translated so that `x*` is the origin,
  `z ↦ f(z + x*)`, because the library semantics is fixed at the origin
  (`Sentence.holds (.flow P) s = P.holds s.zeroInput 0`). Every flow sentence is invariant under
  this translation (`Flow.Property.holds_shift_iff`), so the sentences speak about `x*` itself.

The requirement language is static: `x*` is an equilibrium (`h θ* = 0`, and `K_i ≠ 0` or
`δω = 0`); the slope-gain products of the Jacobian `[[K_p g, K_i], [g, 0]]`, `g = h'(θ*)`, are
negative (trace `< 0`, determinant `> 0`); or one of them is positive (determinant `< 0` or trace
`> 0`). The local sentences translate into the first two, instability into the first and the
third, passivity into nothing, and the global sentences, decay rates, sampled contraction and
conservation — which a local linearization cannot decide — into the whole (inconsistent) language.

The translation chain lies below the semantics connection (`chain_le_semantics`): LeanForControl's
linearization theorems, applied to the field at `x*` and moved to the origin. Passivity is exact
(`exact_passive`). Members are placed in the local denotations by slope and gain conditions alone
(`mem_den_locallyExponentiallyStable`, `mem_den_unstable`, …), and the synchronous-reference-frame
detector `h = −V sin` gives a stable and an unstable member for every `δω`. The frequency-drift
boundary `Σ_FD` of `T-gfl-dynamics` §1.12 is refuted on both the requirement connection and the
semantics connection (`frequencyDriftBoundary_refuted`, `frequencyDriftBoundary_stable`). The
global sentences have no available translation: the linear detector `h = −θ` is globally
exponentially stable, so that translation is sound but not exact
(`not_exact_globallyExponentiallyStable`). At a degenerate slope the local connections part: the
cubic detector `h = −θ³` is Lyapunov stable through the PLL energy `θ⁴/4 + η²/2`
(LeanForControl's `lyapunov_stable`) with a nilpotent Jacobian (`not_exact_lyapunovStable`).
The local exponential translation is exact (`exact_locallyExponentiallyStable`): by the converse
linearization theorem (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`), the selected
point is locally exponentially stable exactly when it is an equilibrium with a Hurwitz Jacobian,
i.e. phase-locked with both slope-gain products negative. The instability translation is not
exact (`not_exact_unstable`): instability is the failure of Lyapunov stability, so a model whose
selected point is not phase-locked (`offEquilibrium`) is unstable
(`offEquilibrium_mem_den_unstable`, `Dynamics.unstable_of_ne_zero`). The local asymptotic
translation is not exact either (`not_exact_locallyAsymptoticallyStable`): the cubic detector is
locally asymptotically stable (`cubicDetector_mem_den_locallyAsymptoticallyStable`, LaSalle's
principle through `Dynamics.LaSalle.tendsto_zero_of_lasalle_detectable`: the PLL energy decreases at the rate
`θ⁶`, and the only solution with `θ ≡ 0` is the locked point) although its slope is zero. -/

noncomputable section


/-! ## The family -/

namespace powerlib.PLL.PIPLL

open Matrix Set

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A PI-PLL model read about a selected operating point: a phase-detector characteristic `h`,
`C¹` on all of `ℝ`, the PI gains, the constant frequency offset and the selected phase `θ*`. -/
structure Model where
  /-- The phase-detector characteristic. -/
  h : ℝ → ℝ
  /-- The proportional gain. -/
  Kp : ℝ
  /-- The integral gain. -/
  Ki : ℝ
  /-- The constant grid-frequency offset `ω_g − ω_s`. -/
  δω : ℝ
  /-- The selected phase `θ*`. -/
  θ : ℝ
  /-- The characteristic is `C¹` on all of `ℝ`. -/
  smooth : ContDiff ℝ 1 h

/-- The selected point `(θ*, δω / K_i)`. -/
def Model.point (m : Model) : ℝ² := PhasePlane.mk m.θ (m.δω / m.Ki)

/-- The PI-PLL field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : ℝ²) : ℝ² := piPLLField m.h m.Kp m.Ki m.δω (z + m.point)

@[powerlib_foundation] theorem Model.hasDerivAt (m : Model) (x : ℝ) :
    HasDerivAt m.h (deriv m.h x) x :=
  ((m.smooth.differentiable one_ne_zero) x).hasDerivAt

/-- Requirements on the PI-PLL models, all static. -/
inductive Requirement
  /-- The selected point is an equilibrium: `h θ* = 0`, and `K_i ≠ 0` or `δω = 0`. -/
  | phaseLocked
  /-- Both slope-gain products negative: trace `K_p h'(θ*) < 0`, determinant `−K_i h'(θ*) > 0`. -/
  | slopeStable
  /-- A slope-gain product positive: determinant `< 0` (saddle) or trace `> 0`. -/
  | slopeUnstable

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .phaseLocked => m.h m.θ = 0 ∧ (m.Ki ≠ 0 ∨ m.δω = 0)
  | .slopeStable => m.Kp * deriv m.h m.θ < 0 ∧ m.Ki * deriv m.h m.θ < 0
  | .slopeUnstable => 0 < m.Ki * deriv m.h m.θ ∨ 0 < m.Kp * deriv m.h m.θ

/-- The translation of the sentences: the local ones into a phase-locked point with negative
slope-gain products, instability into one with a positive product, passivity into nothing. The
global sentences, decay rates, sampled contraction and conservation are not decided by the
linearization and are translated into the whole language, which no model meets (unavailable
translation coverage, not a usable translation). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.phaseLocked, .slopeStable}
  | .flow .unstable => {.phaseLocked, .slopeUnstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The PI-PLL family: every model read as its field translated to the selected point. -/
def family : Family Model Requirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private)

The old public behavioural theorems of the PI-PLL module, at the selected point of the
untranslated field, are kept as private helpers; the public conclusions are the connection
statements below. -/

/-- A flow sentence of a model is the sentence of the untranslated field at the selected point. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (piPLLField m.h m.Kp m.Ki m.δω) m.point :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Formerly the public `piPLL_locallyExponentiallyStable_of_mul_neg`. -/
private theorem piPLL_locallyExponentiallyStable_of_mul_neg {h : ℝ → ℝ}
    {Kp Ki δω θ g : ℝ} (hh : ContDiff ℝ 1 h) (hzero : h θ = 0) (hderiv : HasDerivAt h g θ)
    (hKpg : Kp * g < 0) (hKig : Ki * g < 0) :
    LocallyExponentiallyStable (piPLLField h Kp Ki δω) (PhasePlane.mk θ (δω / Ki)) := by
  have hKi : Ki ≠ 0 := by
    rintro rfl
    simp at hKig
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two (piPLLJacobian Kp Ki g)
    (contDiff_piPLLField hh) ((piPLLField_eq_zero_iff hKi _).mpr ⟨hzero, rfl⟩)
    (fderiv_piPLLField hderiv) ?_ ?_
  · rw [piPLLJacobian_trace]
    exact hKpg
  · rw [piPLLJacobian_det]
    linarith

/-- Formerly the public `piPLL_unstable_of_mul_pos` and `piPLL_unstable_of_trace_pos`, with the
equilibrium hypothesis generalized from `K_i ≠ 0`: at an equilibrium, a negative determinant or a
positive trace of the Jacobian gives instability. -/
private theorem piPLL_unstable_of_slope {h : ℝ → ℝ} {Kp Ki δω θ g : ℝ}
    (hh : ContDiff ℝ 1 h) (heq : piPLLField h Kp Ki δω (PhasePlane.mk θ (δω / Ki)) = 0)
    (hderiv : HasDerivAt h g θ) (hg : 0 < Ki * g ∨ 0 < Kp * g) :
    Unstable (piPLLField h Kp Ki δω) (PhasePlane.mk θ (δω / Ki)) := by
  rcases hg with hdet | htr
  · refine Criteria.unstable_of_jacobian_det_neg_fin_two (piPLLJacobian Kp Ki g)
      (contDiff_piPLLField hh) heq (fderiv_piPLLField hderiv) ?_
    rw [piPLLJacobian_det]
    linarith
  · refine Criteria.unstable_of_jacobian_trace_pos_fin_two (piPLLJacobian Kp Ki g)
      (contDiff_piPLLField hh) heq (fderiv_piPLLField hderiv) ?_
    rw [piPLLJacobian_trace]
    exact htr

private theorem les_of_meets {m : Model} (hp : Meets m .phaseLocked)
    (hs : Meets m .slopeStable) : m ∈ family.den (.flow .locallyExponentiallyStable) :=
  mem_den_flow_iff.mpr (piPLL_locallyExponentiallyStable_of_mul_neg m.smooth hp.1
    (m.hasDerivAt m.θ) hs.1 hs.2)

private theorem unstable_of_meets {m : Model} (hp : Meets m .phaseLocked)
    (hs : Meets m .slopeUnstable) : m ∈ family.den (.flow .unstable) :=
  mem_den_flow_iff.mpr (piPLL_unstable_of_slope m.smooth (piPLLField_point_eq_zero_iff.mpr hp)
    (m.hasDerivAt m.θ) hs)

/-! ### Soundness of the translation -/

/-- No model has both negative slope-gain products and a positive one: the whole requirement
language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨h1, h2⟩ : Meets m .slopeStable := h .slopeStable
  rcases (h .slopeUnstable : Meets m .slopeUnstable) with h3 | h3 <;> linarith

/-- Every translation of the PI-PLL family is sound: its translation chain lies below its
semantics connection. Negative slope-gain products at a phase-locked point prove the local
sentences, a positive one proves instability (LeanForControl's linearization theorems at the
selected point, moved to the origin), and passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · have hles : Meets m .phaseLocked → Meets m .slopeStable →
        LocallyExponentiallyStable m.field 0 := fun hp hs =>
      family_isAutonomous.mem_den_flow.mp (les_of_meets hp hs)
    rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable =>
      exact (hles (hm .phaseLocked (by simp [translate]))
        (hm .slopeStable (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (hles (hm .phaseLocked (by simp [translate])) (hm .slopeStable (by simp [translate])))
    case locallyExponentiallyStable =>
      exact hles (hm .phaseLocked (by simp [translate])) (hm .slopeStable (by simp [translate]))
    case unstable =>
      exact family_isAutonomous.mem_den_flow.mp (unstable_of_meets
        (hm .phaseLocked (by simp [translate])) (hm .slopeUnstable (by simp [translate])))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- The local exponential translation is exact: a model is locally exponentially stable at its
selected point exactly when the point is phase-locked (`h θ* = 0`, and `K_i ≠ 0` or `δω = 0`) and
both slope-gain products are negative (`K_p h'(θ*) < 0`, `K_i h'(θ*) < 0`). Converse
linearization: local exponential stability of a `C¹` field forces an equilibrium with a Hurwitz
Jacobian `[[K_p g, K_i], [g, 0]]`. -/
@[powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize, mem_den_flow_iff]
  have hJac := fderiv_piPLLField (Kp := m.Kp) (Ki := m.Ki) (δω := m.δω) (x := m.point)
    (m.hasDerivAt (m.point 0))
  change _ ↔ LocallyExponentiallyStable _ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _
    (contDiff_piPLLField m.smooth) hJac, piPLLJacobian_isHurwitz_iff, Model.point,
    piPLLField_point_eq_zero_iff]
  simp [family, translate, Meets, PhasePlane.mk]

/-! ### Members of the local denotations -/

/-- Slope and gain conditions alone place a model in local exponential stability: at a zero
`θ*` of `h`, `K_p h'(θ*) < 0` and `K_i h'(θ*) < 0` (Jacobian trace `< 0`, determinant `> 0`). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hzero : m.h m.θ = 0) (hKp : m.Kp * deriv m.h m.θ < 0) (hKi : m.Ki * deriv m.h m.θ < 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hKi0 : m.Ki ≠ 0 := by
    intro h
    rw [h, zero_mul] at hKi
    exact lt_irrefl 0 hKi
  exact les_of_meets ⟨hzero, Or.inl hKi0⟩ ⟨hKp, hKi⟩

/-- Positive gains: a zero `θ*` of `h` with `h'(θ*) < 0` is locally exponentially stable, for
every constant frequency offset `δω`. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_pos (m : Model)
    (hKp : 0 < m.Kp) (hKi : 0 < m.Ki) (hzero : m.h m.θ = 0) (hg : deriv m.h m.θ < 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_locallyExponentiallyStable m hzero (mul_neg_of_pos_of_neg hKp hg)
    (mul_neg_of_pos_of_neg hKi hg)

/-- Saddle: at a zero `θ*` of `h`, `K_i h'(θ*) > 0` (Jacobian determinant `< 0`) places a model
in instability; no sign condition on `K_p`. -/
@[powerlib_domain] theorem mem_den_unstable (m : Model) (hzero : m.h m.θ = 0)
    (hKi : 0 < m.Ki * deriv m.h m.θ) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hKi0 : m.Ki ≠ 0 := by
    intro h
    rw [h, zero_mul] at hKi
    exact lt_irrefl 0 hKi
  exact unstable_of_meets ⟨hzero, Or.inl hKi0⟩ (Or.inl hKi)

/-- Positive trace: at an equilibrium (`h θ* = 0`, and `K_i ≠ 0` or `δω = 0`),
`K_p h'(θ*) > 0` places a model in instability. -/
@[powerlib_domain] theorem mem_den_unstable_of_trace_pos (m : Model) (hzero : m.h m.θ = 0)
    (hlock : m.Ki ≠ 0 ∨ m.δω = 0) (hKp : 0 < m.Kp * deriv m.h m.θ) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact unstable_of_meets ⟨hzero, hlock⟩ (Or.inr hKp)

/-- Positive integral gain: a zero `θ*` of `h` with `h'(θ*) > 0` is unstable (saddle), for every
`K_p` and every constant frequency offset `δω`. -/
@[powerlib_domain] theorem mem_den_unstable_of_pos (m : Model) (hKi : 0 < m.Ki)
    (hzero : m.h m.θ = 0) (hg : 0 < deriv m.h m.θ) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  mem_den_unstable m hzero (mul_pos hKi hg)

/-! ### The synchronous-reference-frame detector -/

/-- The SRF detector `h(θ) = −V sin θ` with grid voltage amplitude `V`. -/
def srf (V Kp Ki δω θ : ℝ) : Model :=
  ⟨fun x => -V * Real.sin x, Kp, Ki, δω, θ, contDiff_const.mul Real.contDiff_sin⟩

@[powerlib_foundation] theorem srf_deriv (V Kp Ki δω θ : ℝ) :
    deriv (srf V Kp Ki δω θ).h (srf V Kp Ki δω θ).θ = -V * Real.cos θ :=
  ((Real.hasDerivAt_sin θ).const_mul (-V)).deriv

/-- SRF detector with positive amplitude and gains: the phase-locked point `θ* = 0` is locally
exponentially stable for every frequency offset `δω`. -/
@[powerlib_domain] theorem srf_mem_den_locallyExponentiallyStable {V Kp Ki : ℝ} (hV : 0 < V)
    (hKp : 0 < Kp) (hKi : 0 < Ki) (δω : ℝ) :
    connection% (srf V Kp Ki δω 0 ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_locallyExponentiallyStable_of_pos _ hKp hKi (by simp [srf])
    (by rw [srf_deriv, Real.cos_zero]; linarith)

/-- SRF detector with positive amplitude and integral gain: the anti-phase point `θ* = π` is
unstable (saddle) for every `K_p` and every frequency offset `δω`. -/
@[powerlib_domain] theorem srf_mem_den_unstable {V Ki : ℝ} (hV : 0 < V) (hKi : 0 < Ki)
    (Kp δω : ℝ) :
    connection% (srf V Kp Ki δω Real.pi ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_pos _ hKi (by simp [srf]) (by rw [srf_deriv, Real.cos_pi]; linarith)

/-! ### The frequency-drift boundary `Σ_FD` -/

/-- `Σ_FD` (`T-gfl-dynamics` §1.12) on the requirement connection — "if `|δω| > K_p sup |h|`, no
phase is locked" — is refuted: the SRF detector with `V = K_p = K_i = 1`, `δω = 2`, `θ* = 0`
meets the phase-locking requirement although `|δω| = 2 > K_p sup |h| = 1`. -/
@[powerlib_domain] theorem frequencyDriftBoundary_refuted :
    connection% (¬ ∀ (m : Model) (M : ℝ), 0 < m.Kp → 0 < m.Ki → (∀ θ, |m.h θ| ≤ M) →
      m.Kp * M < |m.δω| → m ∉ TMIO.realize Meets {.phaseLocked}) := by
  unfold powerlib.TMIO.Statement
  intro H
  refine H (srf 1 1 1 2 0) 1 one_pos one_pos (fun θ => ?_) (by norm_num [srf]) ?_
  · simpa [srf] using Real.abs_sin_le_one θ
  · rw [TMIO.mem_realize]
    simp [Meets, srf]

/-- On the semantics connection the drift boundary fails as well: beyond it the phase-locked
point of the same SRF model is even locally exponentially stable. -/
@[powerlib_domain] theorem frequencyDriftBoundary_stable :
    connection% (¬ ∀ (m : Model) (M : ℝ), 0 < m.Kp → 0 < m.Ki → (∀ θ, |m.h θ| ≤ M) →
      m.Kp * M < |m.δω| → m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro H
  exact H (srf 1 1 1 2 0) 1 one_pos one_pos
    (fun θ => by simpa [srf] using Real.abs_sin_le_one θ) (by norm_num [srf])
    (srf_mem_den_locallyExponentiallyStable one_pos one_pos one_pos 2)

/-! ### Unavailable coverage of the global sentences -/

/-- The linear detector `h(θ) = −θ` with `K_p = K_i = 1`, `δω = 0`, `θ* = 0`. -/
def linearModel : Model := ⟨fun x => -x, 1, 1, 0, 0, contDiff_id.neg⟩

@[powerlib_foundation] theorem linearModel_field :
    linearModel.field = LinearSystems.affineLinearVectorField !![-1, 1; -1, 0] 0 := by
  funext z
  ext i
  fin_cases i <;>
    simp [linearModel, Model.field, Model.point, LinearSystems.affineLinearVectorField,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The linear detector is globally exponentially stable (the linear hub), with no requirement
translating the global sentence. -/
@[powerlib_domain] theorem linearModel_mem_den_globallyExponentiallyStable :
    connection% (linearModel ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow, linearModel_field]
  exact Linear.globallyExponentiallyStable_of_isHurwitz 0
    ((Criteria.isHurwitz_fin_two_of_iff _ _ _ _).mpr ⟨by norm_num, by norm_num⟩)

/-- The translation of global exponential stability is sound but not exact: its requirement space
is empty while the linear detector satisfies the sentence. -/
@[powerlib_domain] theorem not_exact_globallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := linearModel_mem_den_globallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h] at hmem
  change linearModel ∈ TMIO.realize Meets Set.univ at hmem
  rw [realize_univ] at hmem
  exact hmem

/-! ### A degenerate slope: where the local connections part -/

/-- The cubic detector `h(θ) = −θ³` with `K_p = K_i = 1`, `δω = 0`, `θ* = 0`: phase-locked with
slope `h'(0) = 0`, where the Jacobian is nilpotent and the linearization decides nothing. -/
def cubicDetector : Model := ⟨fun x => -x ^ 3, 1, 1, 0, 0, (contDiff_id.pow 3).neg⟩

@[powerlib_foundation] theorem cubicDetector_field (z : ℝ²) :
    cubicDetector.field z = WithLp.toLp 2 ![-(z 0) ^ 3 + z 1, -(z 0) ^ 3] := by
  ext i
  fin_cases i <;> simp [cubicDetector, Model.field, Model.point]

@[powerlib_foundation] theorem cubicDetector_slope : deriv cubicDetector.h cubicDetector.θ = 0 := by
  have h := (hasDerivAt_pow 3 (0 : ℝ)).neg
  exact h.deriv.trans (by norm_num)

/-- The PLL energy `θ⁴ / 4 + η² / 2` (`−∫ h` plus the integrator energy). -/
def cubicEnergy (z : ℝ²) : ℝ := 1 / 4 * (z 0) ^ 4 + 1 / 2 * (z 1) ^ 2

@[powerlib_foundation] theorem cubicEnergy_hasFDerivAt (z : ℝ²) :
    HasFDerivAt cubicEnergy ((z 0) ^ 3 • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ) +
      z 1 • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ)) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h := ((h0.pow 4).const_mul (1 / 4 : ℝ)).add ((h1.pow 2).const_mul (1 / 2 : ℝ))
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

@[powerlib_foundation] theorem cubicEnergy_lie (z : ℝ²) :
    fderiv ℝ cubicEnergy z (cubicDetector.field z) = -(z 0) ^ 6 := by
  rw [(cubicEnergy_hasFDerivAt z).fderiv, cubicDetector_field]
  simp
  ring

/-- The PLL energy is a Lyapunov function of the cubic detector, hence it is Lyapunov stable
although its linearization is not Hurwitz. -/
@[powerlib_domain] theorem cubicDetector_mem_den_lyapunovStable :
    connection% (cubicDetector ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  refine lyapunov_stable (V := cubicEnergy) (D := Set.univ) two_pos
    ⟨isOpen_univ, Set.mem_univ _, ?_, fun z => (cubicEnergy_hasFDerivAt z).differentiableAt,
      by simp [cubicEnergy], fun z _ hz => ?_, fun z _ => ?_⟩
  · exact (continuous_const.mul
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).continuous.pow 4)).add
      (continuous_const.mul ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).continuous.pow 2))
  · have hne : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    dsimp [cubicEnergy]
    rcases hne with h | h
    · have : 0 < (z 0) ^ 4 := by positivity
      nlinarith [sq_nonneg (z 1)]
    · have : 0 < (z 1) ^ 2 := by positivity
      nlinarith [pow_two_nonneg ((z 0) ^ 2)]
  · rw [cubicEnergy_lie]
    nlinarith [pow_two_nonneg ((z 0) ^ 3)]

/-- The local translations are sound but not exact: the cubic detector is Lyapunov stable at a
phase-locked point with zero slope, which meets no slope-gain requirement. -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := cubicDetector_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets cubicDetector .slopeStable := hmem .slopeStable (by simp [family, translate])
  have := hs.1
  rw [cubicDetector_slope] at this
  simp at this

/-! ### The degenerate slope is locally asymptotically stable -/

@[powerlib_foundation] theorem cubicEnergy_contDiff : ContDiff ℝ 1 cubicEnergy := by
  unfold cubicEnergy
  exact (contDiff_const.mul
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).contDiff.pow 4)).add
    (contDiff_const.mul ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).contDiff.pow 2))

@[powerlib_foundation] theorem cubicEnergy_pos {z : ℝ²} (hz : z ≠ 0) : 0 < cubicEnergy z := by
  have hne : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  dsimp [cubicEnergy]
  rcases hne with h | h
  · have : 0 < (z 0) ^ 4 := by positivity
    nlinarith [sq_nonneg (z 1)]
  · have : 0 < (z 1) ^ 2 := by positivity
    nlinarith [pow_two_nonneg ((z 0) ^ 2)]

/-- The PLL energy bounds the squared norm: `‖z‖² ≤ 4 V(z) + 1/4`. -/
@[powerlib_foundation] theorem norm_sq_le_cubicEnergy (z : ℝ²) :
    ‖z‖ ^ 2 ≤ 4 * cubicEnergy z + 1 / 4 := by
  have hsq : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ, sq_abs]
  rw [hsq]
  dsimp [cubicEnergy]
  nlinarith [sq_nonneg ((z 0) ^ 2 - 1 / 2), sq_nonneg (z 1)]

open scoped Pointwise in
/-- The cubic detector is locally asymptotically stable (LaSalle's principle): the PLL energy
decreases at the rate `θ⁶`, and the only solution along which `θ ≡ 0` is the locked point (then
`θ̇ = η` vanishes too). Its Jacobian `[[0, 1], [0, 0]]` is nilpotent, so the linearization decides
nothing. -/
@[powerlib_domain] theorem cubicDetector_mem_den_locallyAsymptoticallyStable :
    connection% (cubicDetector ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hls := cubicDetector_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hls ⊢
  rw [family_isAutonomous.mem_den_flow] at hls ⊢
  set f := cubicDetector.field with hfdef
  have hf : ContDiff ℝ 1 f :=
    (contDiff_piPLLField cubicDetector.smooth).comp (contDiff_id.add contDiff_const)
  have hVd : Differentiable ℝ cubicEnergy := cubicEnergy_contDiff.differentiable one_ne_zero
  have hdec : ∀ z, fderiv ℝ cubicEnergy z (f z) ≤ 0 := fun z => by
    rw [cubicEnergy_lie]
    nlinarith [pow_two_nonneg ((z 0) ^ 3)]
  have hdet : ∀ φ : ℝ → ℝ², IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0) →
      (∀ t ∈ Set.Ici (0 : ℝ), fderiv ℝ cubicEnergy (φ t) (f (φ t)) = 0) →
      Filter.Tendsto φ Filter.atTop (nhds 0) := by
    intro φ hφ hzero
    have h0 : ∀ t ∈ Set.Ici (0 : ℝ), φ t 0 = 0 := fun t ht => by
      have := hzero t ht
      rw [cubicEnergy_lie] at this
      have h6 : (φ t 0) ^ 6 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp h6
    have h1 : ∀ t ∈ Set.Ici (0 : ℝ), φ t 1 = 0 := fun t ht => by
      have hd := ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
        (x := φ t)).comp_hasDerivWithinAt t (hφ t ht)
      have hc : HasDerivWithinAt (fun s => (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ)
          (φ s)) 0 (Set.Ici 0) t :=
        (hasDerivWithinAt_const t (Set.Ici (0 : ℝ)) (0 : ℝ)).congr
          (fun s hs => h0 s hs) (h0 t ht)
      have heq := (uniqueDiffOn_Ici (0 : ℝ) t ht).eq_deriv _ hd hc
      have heq' : cubicDetector.field (φ t) 0 = 0 := heq
      rw [cubicDetector_field] at heq'
      simpa [h0 t ht] using heq'
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 0] with t ht
    ext i
    fin_cases i
    · exact (h0 t ht).symm
    · exact (h1 t ht).symm
  refine ⟨hls, 1, one_pos, fun t₀ φ hφ _ => ?_⟩
  have hψs : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Set.Ici 0) := by
    have hset : -t₀ +ᵥ Set.Ici t₀ = Set.Ici (0 : ℝ) := by
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, Set.mem_Ici]
      constructor <;> intro h <;> linarith
    have h' := _root_.IsIntegralCurveOn.comp_add_autonomous hφ t₀
    rwa [hset] at h'
  have hclosed : IsClosed {x : ℝ² | cubicEnergy x ≤ cubicEnergy (φ t₀)} :=
    isClosed_le hVd.continuous continuous_const
  have hinv : IsPositivelyInvariant {x | cubicEnergy x ≤ cubicEnergy (φ t₀)} f := by
    have h := Dynamics.LaSalle.isPositivelyInvariant_sublevel_of_isOpen (f := f)
      (c := cubicEnergy (φ t₀)) isOpen_univ hVd (fun x _ => hdec x) (by simpa using hclosed)
    simpa using h
  have hΩ : IsCompact {x : ℝ² | cubicEnergy x ≤ cubicEnergy (φ t₀)} := by
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ²)).mpr
      ⟨4 * cubicEnergy (φ t₀) + 1, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := norm_sq_le_cubicEnergy x
    have h2 : cubicEnergy x ≤ cubicEnergy (φ t₀) := hx
    have h3 : 0 ≤ cubicEnergy x := by
      rcases eq_or_ne x 0 with rfl | hx0
      · simp [cubicEnergy]
      · exact (cubicEnergy_pos hx0).le
    nlinarith [norm_nonneg x]
  have hconv := Dynamics.LaSalle.tendsto_zero_of_lasalle_detectable hf cubicEnergy_contDiff
    (by simp [cubicEnergy]) (fun x hx => cubicEnergy_pos hx) hdec hdet hΩ hinv hψs (by simp)
  exact Filter.Tendsto.congr (fun x => by simp)
    (hconv.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-t₀) Filter.tendsto_id))

/-- The local asymptotic translation is sound but not exact: the cubic detector is locally
asymptotically stable at a phase-locked point with zero slope, which meets no slope-gain
requirement. -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := cubicDetector_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets cubicDetector .slopeStable := hmem .slopeStable (by simp [family, translate])
  have := hs.1
  rw [cubicDetector_slope] at this
  simp at this

/-! ### Instability away from equilibrium -/

/-- A model whose selected point is not phase-locked: the constant detector `h ≡ 1`, all gains
and the offset zero, `θ* = 0`. -/
def offEquilibrium : Model := ⟨fun _ => 1, 0, 0, 0, 0, contDiff_const⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_ne_zero
    (contDiff_piPLLField offEquilibrium.smooth) fun h => ?_)
  have := congrArg (fun y : ℝ² => y 1) h
  simp [offEquilibrium] at this

/-- The instability translation is sound but not exact: instability is the failure of Lyapunov
stability, which every non-equilibrium point satisfies, while the translation asks for a
phase-locked point. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hp : Meets offEquilibrium .phaseLocked := hmem .phaseLocked (by simp [family, translate])
  simp [Meets, offEquilibrium] at hp

end powerlib.PLL.PIPLL
