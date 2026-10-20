import theorem.PLL.PIPLL
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.LaSalle.Passivity
import theorem.Spectral.Local

/-! # The PI-PLL family

The family of PI phase-locked loops with a general phase-detector characteristic and its
connection conclusions; the static model (field, Jacobian, equilibria) is
`theorem/PLL/PIPLL.lean`.

Model boundary.
A complete system is a PI phase-locked loop with a general phase-detector
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
  this translation (`Flow.Property.holds_shift_iff`), so the sentences speak about `x*` itself;
* a grid-frequency ramp `δω(t) = δω + ρ t` is not a parameter: the ramped loop is read through the
  ramp model `m.ramp ρ` (detector `h − ρ/K_i`, offset `0`, selected point `(θ*, 0)`), to which it
  is equivalent in the coordinates `(θ, η − δω(t)/K_i + K_p ρ/K_i²)` when `K_i ≠ 0`
  (`ramp_hasDerivAt_iff`).

Source: work-sync `theory/T-gfl-dynamics.md` §1.7 (boxed 2D ODE), §1.9 (equilibria), §1.10
(Jacobian and local stability), §1.12 (`Σ_FD`: constant offset and frequency ramp).

Results.
Static evidence on the members (the behavioural results are the connection conclusions below):
* `family_isAutonomous`, `Model.hasDerivAt`: the system map is the translated autonomous field.
* `realize_univ`: the whole requirement language is inconsistent.
* `srf_deriv`, `linearModel_field`, `cubicDetector_field`, `cubicDetector_slope`: the SRF, linear
  (`h = −θ`) and cubic (`h = −θ³`) detector members.
* `cubicEnergy_hasFDerivAt`, `cubicEnergy_lie`, `cubicEnergy_contDiff`, `cubicEnergy_pos`,
  `norm_sq_le_cubicEnergy`: the PLL energy `θ⁴/4 + η²/2` of the cubic detector.
* `Model.ramp`, `Model.ramp_deriv`, `ramp_hasDerivAt_iff`: the ramp model (detector `h − ρ/K_i`,
  with the slope of `h`, no offset) and the bridge from the loop under a frequency ramp to it.

Family and connection conclusions.
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
detector `h = −V sin` gives a stable and an unstable member for every `δω`. A negative slope with
`K_p ≥ 0`, `K_i > 0` gives Lyapunov stability through the PLL energy `U(θ) + ½ K_i (η − δω/K_i)²`,
`U = −∫_{θ*} h`, also for the lossless loop `K_p = 0` whose linearization is a centre
(`mem_den_lyapunovStable_of_slope`). At a hyperbolic slope (`K_p h'(θ*) ≠ 0`, `K_i h'(θ*) ≠ 0`)
local asymptotic stability is decided by the linearization: it holds exactly at a phase-locked
point with both products negative (`mem_den_las_iff_of_nondegenerate`). The frequency-drift
boundary `Σ_FD` as `T-gfl-dynamics` §1.12 first stated it — a constant offset `|δω| > K_p sup |h|`
removes phase lock — is refuted on both the requirement connection and the semantics connection
(`frequencyDriftBoundary_refuted`, `frequencyDriftBoundary_stable`): the integrator absorbs a
constant offset. The note now states the boundary for a frequency ramp `δω(t) = δω + ρ t`, which
in the coordinates `(θ, η − δω(t)/K_i + K_p ρ/K_i²)` is the member `m.ramp ρ` of this family, with
the detector `h − ρ/K_i` and no offset (`ramp_hasDerivAt_iff`). Its phase-locked phases are the
solutions of `h(θ*) = ρ/K_i` (`ramp_phaseLocked_iff`). When `ρ/K_i` leaves the range of `h` —
across `Σ_FD`: `ρ = K_i max h` or `ρ = K_i min h` — no phase is locked and every ramp model is
unstable: the loop loses lock (`frequencyRampBoundary`). Within the range, local exponential
stability of a ramp model is decided by the slope `h'(θ*)` at a locked phase as for any model
(`ramp_mem_den_locallyExponentiallyStable_iff`), and local asymptotic stability too at a
hyperbolic slope (`ramp_mem_den_las_iff_of_nondegenerate`). The global sentences have no
available translation: the linear detector `h = −θ` is globally exponentially stable, so that
translation is sound but not exact (`not_exact_globallyExponentiallyStable`). At a degenerate
slope the local connections part: the cubic detector `h = −θ³` is Lyapunov stable through the PLL
energy `θ⁴/4 + η²/2` (LeanForControl's `lyapunov_stable`) with a nilpotent Jacobian
(`not_exact_lyapunovStable`).
The local exponential translation is exact (`exact_locallyExponentiallyStable`): by the converse
linearization theorem (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`), the selected
point is locally exponentially stable exactly when it is an equilibrium with a Hurwitz Jacobian,
i.e. phase-locked with both slope-gain products negative. The instability translation is not
exact (`not_exact_unstable`): instability is the failure of Lyapunov stability, so every model
whose selected point is not phase-locked is unstable (`mem_den_unstable_of_not_phaseLocked`,
`Dynamics.unstable_of_ne_zero`), e.g. `offEquilibrium` (`offEquilibrium_mem_den_unstable`). The
local asymptotic translation is not exact either (`not_exact_locallyAsymptoticallyStable`): the
cubic detector is locally asymptotically stable
(`cubicDetector_mem_den_locallyAsymptoticallyStable`, LaSalle's principle through
`Dynamics.LaSalle.tendsto_zero_of_lasalle_detectable`: the PLL energy decreases at the rate `θ⁶`,
and the only solution with `θ ≡ 0` is the locked point) although its slope is zero.
-/

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

Behavioural statements at the selected point of the untranslated field, used as private
helpers; the public conclusions are the connection statements below. -/

/-- A flow sentence of a model is the sentence of the untranslated field at the selected point. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (piPLLField m.h m.Kp m.Ki m.δω) m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => piPLLField m.h m.Kp m.Ki m.δω)
    (pt := Model.point) family_isAutonomous

/-- At an equilibrium with both slope-gain products negative (`K_p g < 0`, `K_i g < 0`) the
untranslated field is locally exponentially stable. -/
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

/-- At an equilibrium (no hypothesis `K_i ≠ 0` needed), a negative determinant or a positive
trace of the Jacobian gives instability. -/
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
  refine Spectral.realize_univ_eq_empty_of .slopeStable .slopeUnstable fun m hs hu => ?_
  obtain ⟨h1, h2⟩ : Meets m .slopeStable := hs
  rcases (hu : Meets m .slopeUnstable) with h3 | h3 <;> linarith

/-- Every translation of the PI-PLL family is sound: its translation chain lies below its
semantics connection. Negative slope-gain products at a phase-locked point prove the local
sentences, a positive one proves instability (LeanForControl's linearization theorems at the
selected point, moved to the origin), and passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (Rs := {.phaseLocked, .slopeStable})
    (Ru := {.phaseLocked, .slopeUnstable}) (fun s => ?_) realize_univ (fun m hm => ?_)
    (fun m hm => ?_) family_isAutonomous.den_passive
  · rcases s with P | _
    · cases P <;> rfl
    · rfl
  · rw [TMIO.mem_realize] at hm
    exact les_of_meets (hm .phaseLocked (by simp)) (hm .slopeStable (by simp))
  · rw [TMIO.mem_realize] at hm
    exact unstable_of_meets (hm .phaseLocked (by simp)) (hm .slopeUnstable (by simp))

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
  refine Spectral.exact_of_exactUnder_empty (Spectral.exactUnder_les_of_jacobian
    (fun m P => mem_den_flow_iff) ∅ (fun m => piPLLJacobian m.Kp m.Ki (deriv m.h (m.point 0)))
    (fun m _ hm => ?_) (fun m _ => contDiff_piPLLField m.smooth)
    (fun m _ => fderiv_piPLLField (m.hasDerivAt (m.point 0))) fun m _ heq hH => ?_)
  · rw [TMIO.mem_realize] at hm
    exact les_of_meets (hm .phaseLocked (by simp [family, translate]))
      (hm .slopeStable (by simp [family, translate]))
  rw [Model.point, piPLLField_point_eq_zero_iff] at heq
  rw [piPLLJacobian_isHurwitz_iff, Model.point, PhasePlane.mk_apply_zero] at hH
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl)
  · exact heq
  · exact hH

/-- At a hyperbolic slope — both slope-gain products nonzero, so that the Jacobian
`[[K_p g, K_i], [g, 0]]` has nonzero trace and determinant and no eigenvalue on the imaginary
axis — local asymptotic stability is decided by the linearization: a model is locally
asymptotically stable at its selected point exactly when the point is phase-locked with both
products negative (a Hurwitz Jacobian). A locally asymptotically stable point of the `C¹` field is
an equilibrium (`Dynamics.isEquilibrium_of_lyapunovStable`), and at an equilibrium a positive
determinant-side product (`K_i g > 0`, a saddle) or a positive trace (`K_p g > 0`) is unstable. -/
@[powerlib_domain] theorem mem_den_las_iff_of_nondegenerate (m : Model)
    (hKp : m.Kp * deriv m.h m.θ ≠ 0) (hKi : m.Ki * deriv m.h m.θ ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ TMIO.realize Meets {.phaseLocked, .slopeStable}) := by
  unfold powerlib.TMIO.Statement
  constructor
  · intro hd
    have hlas := mem_den_flow_iff.mp hd
    have heq : piPLLField m.h m.Kp m.Ki m.δω m.point = 0 :=
      Dynamics.isEquilibrium_of_lyapunovStable (contDiff_piPLLField m.smooth) hlas.1
    have hneg : ∀ {c : ℝ}, c ≠ 0 → (0 < c → Unstable (piPLLField m.h m.Kp m.Ki m.δω) m.point) →
        c < 0 := fun hc hu =>
      (lt_or_gt_of_ne hc).resolve_right fun hpos => hu hpos hlas.1
    rw [TMIO.mem_realize]
    rintro q (rfl | rfl)
    · exact piPLLField_point_eq_zero_iff.mp heq
    · exact ⟨hneg hKp fun h => piPLL_unstable_of_slope m.smooth heq (m.hasDerivAt m.θ) (Or.inr h),
        hneg hKi fun h => piPLL_unstable_of_slope m.smooth heq (m.hasDerivAt m.θ) (Or.inl h)⟩
  · intro hm
    rw [TMIO.mem_realize] at hm
    exact Spectral.den_locallyExponentiallyStable_subset_las
      (les_of_meets (hm .phaseLocked (by simp)) (hm .slopeStable (by simp)))

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

/-- Off the phase-locked set every model is unstable: a selected point that is not phase-locked
(`h θ* ≠ 0`, or `K_i = 0` with an offset `δω ≠ 0`) is not an equilibrium of the `C¹` field, so
the solution through it leaves it (`Spectral.mem_den_unstable_of_ne_zero`). -/
@[powerlib_domain] theorem mem_den_unstable_of_not_phaseLocked (m : Model)
    (hm : m ∉ TMIO.realize Meets {.phaseLocked}) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff)
    (contDiff_piPLLField m.smooth) fun h => hm ?_
  rw [TMIO.mem_realize]
  rintro q rfl
  exact piPLLField_point_eq_zero_iff.mp h

/-! ### Lyapunov stability at a negative slope: the PLL energy

At a zero `θ*` of `h` with `h'(θ*) < 0`, `K_p ≥ 0` and `K_i > 0` the PLL energy
`E(θ, η) = U(θ) + ½ K_i (η − δω/K_i)²`, `U(θ) = −∫_{θ*}^{θ} h`, is a local Lyapunov function of
the untranslated field at the selected point: `Ė = −K_p h(θ)² ≤ 0`, and `U > 0` near `θ*` off
`θ*`, because `h` decreases through zero there. The lossless loop `K_p = 0` is included, where the
linearization (a centre) decides nothing. Implementation evidence; the public conclusion is
`mem_den_lyapunovStable_of_slope`. -/

/-- The detector potential about the selected phase, `U(θ) = −∫_{θ*}^{θ} h`. -/
private def potential (m : Model) (θ : ℝ) : ℝ := -∫ s in m.θ..θ, m.h s

private theorem hasDerivAt_potential (m : Model) (θ : ℝ) :
    HasDerivAt (potential m) (-m.h θ) θ :=
  (m.smooth.continuous.integral_hasStrictDerivAt m.θ θ).hasDerivAt.neg

/-- The PLL energy `E(θ, η) = U(θ) + ½ K_i (η − δω/K_i)²`. -/
private def energy (m : Model) (x : ℝ²) : ℝ :=
  potential m (x 0) + m.Ki / 2 * (x 1 - m.δω / m.Ki) ^ 2

private theorem hasFDerivAt_energy (m : Model) (x : ℝ²) :
    HasFDerivAt (energy m)
      ((-m.h (x 0)) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ) +
        (m.Ki * (x 1 - m.δω / m.Ki)) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ)) x := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := ((hasDerivAt_potential m (x 0)).comp_hasFDerivAt x h0).add
    (((h1.sub_const (m.δω / m.Ki)).pow 2).const_mul (m.Ki / 2))
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

/-- The energy decreases at the damping rate: `Ė = −K_p h(θ)²` (`K_i ≠ 0`). -/
private theorem energy_lie (m : Model) (hKi : m.Ki ≠ 0) (x : ℝ²) :
    fderiv ℝ (energy m) x (piPLLField m.h m.Kp m.Ki m.δω x) = -(m.Kp * m.h (x 0) ^ 2) := by
  rw [(hasFDerivAt_energy m x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul, piPLLField_apply_zero, piPLLField_apply_one]
  field_simp
  ring

/-- Near a zero `θ*` of `h` where the slope stays negative the potential is positive off `θ*`:
`h > 0` before `θ*` and `h < 0` after it. -/
private theorem potential_pos (m : Model) (hzero : m.h m.θ = 0) {r : ℝ}
    (hr : ∀ θ, |θ - m.θ| < r → deriv m.h θ < 0) {θ : ℝ} (hθ : |θ - m.θ| < r) (hne : θ ≠ m.θ) :
    0 < potential m θ := by
  have hanti : StrictAntiOn m.h (Set.Ioo (m.θ - r) (m.θ + r)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) m.smooth.continuous.continuousOn
      fun s hs => ?_
    rw [interior_Ioo] at hs
    exact hr s (abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  obtain ⟨hθ1, hθ2⟩ := abs_lt.mp hθ
  have hmem : m.θ ∈ Set.Ioo (m.θ - r) (m.θ + r) := ⟨by linarith, by linarith⟩
  have hint : ∀ a b, IntervalIntegrable m.h MeasureTheory.volume a b := fun a b =>
    m.smooth.continuous.intervalIntegrable a b
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [potential, ← intervalIntegral.integral_symm]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _) (fun s hs => ?_) hlt
    have := hanti ⟨by linarith [hs.1], by linarith [hs.2]⟩ hmem hs.2
    rwa [hzero] at this
  · rw [potential, ← intervalIntegral.integral_neg]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _).neg (fun s hs => ?_) hgt
    have := hanti hmem ⟨by linarith [hs.1], by linarith [hs.2]⟩ hs.1
    rw [hzero] at this
    exact neg_pos.mpr this

/-- At a zero of `h` with negative slope, `K_p ≥ 0` and `K_i > 0`, the untranslated field is
Lyapunov stable at the selected point (the PLL energy, LeanForControl's `lyapunov_stable`). -/
private theorem lyapunovStable_of_slope {m : Model} (hzero : m.h m.θ = 0) (hKp : 0 ≤ m.Kp)
    (hKi : 0 < m.Ki) (hg : deriv m.h m.θ < 0) :
    LyapunovStable (piPLLField m.h m.Kp m.Ki m.δω) m.point := by
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (m.smooth.continuous_deriv le_rfl) continuous_const) m.θ hg
  have hr' : ∀ θ, |θ - m.θ| < r → deriv m.h θ < 0 := fun θ hθ =>
    hr (by simpa [Real.dist_eq] using hθ)
  have hp0 : m.point 0 = m.θ := by simp [Model.point]
  have hp1 : m.point 1 = m.δω / m.Ki := by simp [Model.point]
  have hEd : Differentiable ℝ (energy m) := fun x => (hasFDerivAt_energy m x).differentiableAt
  apply lyapunov_stable (D := {x : ℝ² | |x 0 - m.θ| < r}) (V := energy m) (by norm_num)
  refine ⟨?_, ?_, hEd.continuous, hEd, ?_, fun x hx hne => ?_, fun x _ => ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_const
  · show |m.point 0 - m.θ| < r
    simpa [hp0] using hr0
  · simp [energy, potential, hp0, hp1]
  · have hx' : |x 0 - m.θ| < r := hx
    have hq : 0 ≤ m.Ki / 2 * (x 1 - m.δω / m.Ki) ^ 2 := by positivity
    by_cases h0 : x 0 = m.θ
    · have h1 : x 1 - m.δω / m.Ki ≠ 0 := fun h1 => hne (PhasePlane.ext_iff'.2
        ⟨by rw [h0, hp0], by rw [hp1]; linarith⟩)
      have : 0 < m.Ki / 2 * (x 1 - m.δω / m.Ki) ^ 2 := by positivity
      simpa [energy, potential, h0] using this
    · have hU := potential_pos m hzero hr' hx' h0
      simp only [energy]
      linarith
  · rw [energy_lie m hKi.ne']
    nlinarith [sq_nonneg (m.h (x 0))]

/-- At a zero `θ*` of `h` with negative slope `h'(θ*) < 0`, a nonnegative proportional gain and a
positive integral gain place a model in Lyapunov stability, for every constant offset `δω`: the PLL
energy `U(θ) + ½ K_i (η − δω/K_i)²`, `U = −∫_{θ*} h`, decreases at the rate `K_p h(θ)²`. With
`K_p = 0` (a lossless loop, a centre of the linearization) the energy is conserved. -/
@[powerlib_domain] theorem mem_den_lyapunovStable_of_slope (m : Model) (hzero : m.h m.θ = 0)
    (hKp : 0 ≤ m.Kp) (hKi : 0 < m.Ki) (hg : deriv m.h m.θ < 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (lyapunovStable_of_slope hzero hKp hKi hg)

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

/-! ### The frequency-ramp boundary `Σ_FD`

A grid frequency ramping as `δω(t) = δω + ρ t` makes the PI-PLL non-autonomous. In the
coordinates `(θ, η̂)`, `η̂ = η − δω(t)/K_i + K_p ρ/K_i²`, it is the autonomous member `m.ramp ρ`
of this family: the detector `h − ρ/K_i`, no offset, the same gains (`ramp_hasDerivAt_iff`). -/

/-- The ramp model of `m` at the ramp rate `ρ`: the PI-PLL with the detector `h − ρ/K_i`, no
frequency offset, the gains and the selected phase of `m`; its selected point is `(θ*, 0)`. -/
def Model.ramp (m : Model) (ρ : ℝ) : Model :=
  ⟨fun θ => m.h θ - ρ / m.Ki, m.Kp, m.Ki, 0, m.θ, m.smooth.sub contDiff_const⟩

/-- The tilted detector `h − ρ/K_i` has the slope of `h`. -/
@[simp, powerlib_foundation] theorem Model.ramp_deriv (m : Model) (ρ θ : ℝ) :
    deriv (m.ramp ρ).h θ = deriv m.h θ :=
  deriv_sub_const _

/-- Bridge to the original law under a frequency ramp (`K_i ≠ 0`): `(θ, η)` solves
`θ̇ = K_p h(θ) + K_i η − (δω + ρ t)`, `η̇ = h(θ)` at time `t` iff
`z = (θ − θ*, η̂)`, `η̂ = η − (δω + ρ t)/K_i + K_p ρ/K_i²`, solves `ż = f(z)` at `t` for the field
`f` of the ramp model `m.ramp ρ` — the state of the family, translated to the selected point
`(θ*, 0)` — written componentwise. -/
@[powerlib_foundation] theorem ramp_hasDerivAt_iff (m : Model) (ρ : ℝ) (hKi : m.Ki ≠ 0)
    (θ η : ℝ → ℝ) (t : ℝ) :
    (HasDerivAt θ (m.Kp * m.h (θ t) + m.Ki * η t - (m.δω + ρ * t)) t ∧
        HasDerivAt η (m.h (θ t)) t) ↔
      (HasDerivAt (fun s => θ s - m.θ) ((m.ramp ρ).field (PhasePlane.mk (θ t - m.θ)
          (η t - (m.δω + ρ * t) / m.Ki + m.Kp * ρ / m.Ki ^ 2)) 0) t ∧
        HasDerivAt (fun s => η s - (m.δω + ρ * s) / m.Ki + m.Kp * ρ / m.Ki ^ 2)
          ((m.ramp ρ).field (PhasePlane.mk (θ t - m.θ)
            (η t - (m.δω + ρ * t) / m.Ki + m.Kp * ρ / m.Ki ^ 2)) 1) t) := by
  rw [hasDerivAt_sub_const_iff]
  simp only [Model.field, Model.point, Model.ramp, piPLLField_apply_zero, piPLLField_apply_one,
    PiLp.add_apply, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, sub_add_cancel, zero_div,
    add_zero]
  have hc : HasDerivAt (fun s => (m.δω + ρ * s) / m.Ki - m.Kp * ρ / m.Ki ^ 2) (ρ / m.Ki) t := by
    simpa using ((((hasDerivAt_id t).const_mul ρ).const_add m.δω).div_const m.Ki).sub_const
      (m.Kp * ρ / m.Ki ^ 2)
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0.congr_deriv (by field_simp; ring), ?_⟩
    convert h1.sub hc using 1
    funext s
    simp only [Pi.sub_apply]
    ring
  · rintro ⟨h0, h1⟩
    refine ⟨h0.congr_deriv (by field_simp; ring), ?_⟩
    convert h1.add hc using 1
    · funext s
      simp only [Pi.add_apply]
      ring
    · ring

/-- Under a frequency ramp `ρ` the phase-locked phases are the solutions of `h(θ*) = ρ / K_i`:
the ramp model meets the phase-locking requirement exactly there (it has no offset, so no
condition on `K_i` remains). -/
@[powerlib_domain] theorem ramp_phaseLocked_iff (m : Model) (ρ : ℝ) :
    connection% (m.ramp ρ ∈ TMIO.realize Meets {.phaseLocked} ↔ m.h m.θ = ρ / m.Ki) := by
  unfold powerlib.TMIO.Statement
  simp [Meets, Model.ramp, sub_eq_zero]

/-- `Σ_FD` (`T-gfl-dynamics` §1.12) for a frequency ramp: when `ρ / K_i` lies outside the range
of `h` — above every value or below every value, i.e. beyond `ρ = K_i max h` or
`ρ = K_i min h` — no phase is locked under the ramp (`ramp_phaseLocked_iff`), and every ramp
model, whatever its selected phase, is unstable (`mem_den_unstable_of_not_phaseLocked`): the PLL
loses lock. -/
@[powerlib_domain] theorem frequencyRampBoundary (m : Model) (ρ : ℝ)
    (hρ : ρ / m.Ki ∉ Set.range m.h) :
    connection% (m.ramp ρ ∈ family.den (.flow .unstable)) := by
  have hlock := ramp_phaseLocked_iff m ρ
  unfold powerlib.TMIO.Statement at hlock ⊢
  exact mem_den_unstable_of_not_phaseLocked _ fun hm => hρ ⟨m.θ, hlock.mp hm⟩

/-- The ramp model meets the local requirements exactly at a locked phase with both slope-gain
products negative. -/
private theorem ramp_mem_realize_iff (m : Model) (ρ : ℝ) :
    m.ramp ρ ∈ TMIO.realize Meets {.phaseLocked, .slopeStable} ↔
      m.h m.θ = ρ / m.Ki ∧ m.Kp * deriv m.h m.θ < 0 ∧ m.Ki * deriv m.h m.θ < 0 := by
  simp [Meets, Model.ramp, sub_eq_zero]

/-- Local exponential stability of a ramp model is decided by the slope as for any model
(`exact_locallyExponentiallyStable`): it holds exactly at a locked phase, `h(θ*) = ρ / K_i` (so
`ρ / K_i` lies in the range of `h`), with both slope-gain products at `θ*` negative — the tilted
detector `h − ρ/K_i` has the slope of `h`. -/
@[powerlib_domain] theorem ramp_mem_den_locallyExponentiallyStable_iff (m : Model) (ρ : ℝ) :
    connection% (m.ramp ρ ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.h m.θ = ρ / m.Ki ∧ m.Kp * deriv m.h m.θ < 0 ∧ m.Ki * deriv m.h m.θ < 0) := by
  have hex := exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement Family.Exact at hex
  unfold powerlib.TMIO.Statement
  rw [← hex]
  exact ramp_mem_realize_iff m ρ

/-- At a hyperbolic slope (both slope-gain products nonzero) local asymptotic stability of a ramp
model is decided in the same way (`mem_den_las_iff_of_nondegenerate`). -/
@[powerlib_domain] theorem ramp_mem_den_las_iff_of_nondegenerate (m : Model) (ρ : ℝ)
    (hKp : m.Kp * deriv m.h m.θ ≠ 0) (hKi : m.Ki * deriv m.h m.θ ≠ 0) :
    connection% (m.ramp ρ ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m.h m.θ = ρ / m.Ki ∧ m.Kp * deriv m.h m.θ < 0 ∧ m.Ki * deriv m.h m.θ < 0) := by
  have hlas := mem_den_las_iff_of_nondegenerate (m.ramp ρ) (by simpa [Model.ramp] using hKp)
    (by simpa [Model.ramp] using hKi)
  unfold powerlib.TMIO.Statement at hlas ⊢
  rw [hlas]
  exact ramp_mem_realize_iff m ρ

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
  exact Spectral.not_exact_of_witness linearModel_mem_den_globallyExponentiallyStable
    (q := .slopeUnstable) trivial (by simp [family, Meets, linearModel])

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
  exact Spectral.not_exact_of_witness cubicDetector_mem_den_lyapunovStable (q := .slopeStable)
    (by simp [family, translate]) (by simp [family, Meets, cubicDetector_slope])

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
  exact Spectral.not_exact_of_witness cubicDetector_mem_den_locallyAsymptoticallyStable
    (q := .slopeStable) (by simp [family, translate]) (by simp [family, Meets, cubicDetector_slope])

/-! ### Instability away from equilibrium -/

/-- A model whose selected point is not phase-locked: the constant detector `h ≡ 1`, all gains
and the offset zero, `θ* = 0`. -/
def offEquilibrium : Model := ⟨fun _ => 1, 0, 0, 0, 0, contDiff_const⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it
(`mem_den_unstable_of_not_phaseLocked`). -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_not_phaseLocked _ (by simp [Meets, offEquilibrium])

/-- The instability translation is sound but not exact: instability is the failure of Lyapunov
stability, which every non-equilibrium point satisfies, while the translation asks for a
phase-locked point. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .phaseLocked)
    (by simp [family, translate]) (by simp [family, Meets, offEquilibrium])

end powerlib.PLL.PIPLL
