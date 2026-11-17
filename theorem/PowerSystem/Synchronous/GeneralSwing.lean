import theorem.PowerSystem.Synchronous.Swing
import theorem.Spectral.Family

/-! # The swing equation with an arbitrary power law

The swing equation `M θ̈ + D θ̇ = τ − P_e(θ, θ̇)` with an arbitrary electrical power law, read about
a free selected point `(θ*, ω*)`. Its spokes are matching control
(`theorem/GridTiedConverter/GFM/Matching/Matching.lean`, by the change of coordinates
`(θ, v) ↦ (θ, η v)`) and the VSM with an arbitrary power map
(`theorem/GridTiedConverter/GFM/DroopVSM.lean`, by an equality of fields); on a speed-independent
sinusoidal law with `ω* = 0` it is the canonical swing model of
`theorem/PowerSystem/Synchronous/Swing.lean`.

Model boundary.
* State `(θ, ω) : Dynamics.State 2`: an angle relative to a rotating reference and its rate
  `ω = θ̇`; continuous time, autonomous, no input (the driving power `τ` is constant).
* Dynamics `θ̇ = ω`, `M ω̇ = τ − P_e(θ, ω) − D ω` with an arbitrary law `P_e : ℝ → ℝ → ℝ`
  (export-positive; it may depend on the speed, as the matched load law of matching control does
  when the load current depends on the DC voltage); `M, D, τ` are free. Smoothness of the law
  enters only as a hypothesis (`contDiffAt_field`,
  `theorem/PowerSystem/Synchronous/SwingEuler.lean`).
* The selected point `(θ*, ω*)` is free (not necessarily an equilibrium, `ω*` not necessarily
  zero).

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.2 (the matched swing equation);
`theory/T-vsg-control.md` §1.2, §1.9; `theory/T-gfm-control.md` §1.6.

Results.
* `family_isAutonomous`: the family reads every model as the autonomous translated field
  `Model.field`, so its denotations are the generic flow denotations of that field.

Family and connection conclusions.
* `GeneralSwing.family : Family Model Spectral.Requirement 2 0` reads a model as its field
  translated so that the selected point is the origin (`Spectral.localFamily`). It has no
  requirement language of its own (both conditions are `False`): every flow translation is
  unavailable coverage, sound because it is empty (`chain_le_semantics`), and passivity is exact.
  Its content is its semantics; its spokes read through it (`GFM.Matching.matching_den_eq`,
  `GFM.DroopVSM.vsm_den_eq_preimage`).
* `mem_den_iff_hub_of_sinusoid` (connection comparison): on a speed-independent sinusoidal law
  `P_e(θ, ω) = k₁ + k₂ sin(θ − k₃)` with `ω* = 0` a model is the canonical swing model
  `⟨M, D, τ, k₁, k₂, k₃⟩` of `Synchronous.Swing.family` about `θ*` (the two translated fields are
  equal); through that hub `mem_den_locallyExponentiallyStable_iff_of_sinusoid` characterizes local
  exponential stability (`M > 0`) by balance, `D > 0` and `k₂ cos(θ* − k₃) > 0`
  (`Synchronous.Swing.exactUnder_locallyExponentiallyStable`). The family stays one of its own: its
  law may depend on the speed and its selected speed is free, while the hub has the
  speed-independent sinusoid and the point `(δ*, 0)`. Without a requirement language there is
  nothing for `Spectral.exactUnder_of_hub` to carry: the hub supplies the denotations themselves on
  the sinusoidal case. Scaffold: `theorem/PowerSystem/Synchronous/GeneralSwing.agda`.
-/

noncomputable section
namespace powerlib.Synchronous.GeneralSwing
open powerlib.Dynamics (State)

/-- The swing field with an arbitrary power law, state `(θ, ω)`: `M ω̇ = τ − P_e(θ, ω) − D ω`. -/
def field (M D τ : ℝ) (Pe : ℝ → ℝ → ℝ) (y : State 2) : State 2 :=
  PhasePlane.mk (y 1) ((τ - Pe (y 0) (y 1) - D * y 1) / M)

/-- A swing model with an arbitrary electrical power law and a selected point `(θ*, ω*)`. -/
structure Model where
  /-- Inertia. -/
  M : ℝ
  /-- Damping. -/
  D : ℝ
  /-- Driving (mechanical or reference) power. -/
  τ : ℝ
  /-- The electrical power law `P_e(θ, ω)`. -/
  Pe : ℝ → ℝ → ℝ
  /-- The selected angle `θ*`. -/
  θ : ℝ
  /-- The selected speed `ω*`. -/
  ω : ℝ

namespace Model

/-- The selected point `(θ*, ω*)`. -/
def point (m : Model) : State 2 := PhasePlane.mk m.θ m.ω

/-- The swing field translated so that the selected point is the origin. -/
def field (m : Model) (z : State 2) : State 2 :=
  GeneralSwing.field m.M m.D m.τ m.Pe (z + m.point)

end Model

/-- The swing family with an arbitrary power law: no requirement language of its own; its content
is its semantics. -/
def family : Family Model Spectral.Requirement 2 0 :=
  Spectral.localFamily Model.field (fun _ => False) (fun _ => False)

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  Spectral.localFamily_isAutonomous _ _ _

/-- Every translation of the swing family is sound: no member meets a requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_chain_le_semantics (fun _ h => h.elim) (fun _ h => h.elim)

/-- On a speed-independent sinusoidal power law `P_e(θ, ω) = k₁ + k₂ sin(θ − k₃)` and at a selected
point with `ω* = 0`, a swing model is the canonical swing model `⟨M, D, τ, k₁, k₂, k₃⟩` of
`Synchronous.Swing.family` read about `θ*`: the two families agree on every sentence, because the
two translated fields are equal. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_hub_of_sinusoid (m : Model) (k₁ k₂ k₃ : ℝ)
    (hP : m.Pe = fun θ _ => k₁ + k₂ * Real.sin (θ - k₃)) (hω : m.ω = 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔
      Swing.Model.mk ⟨m.M, m.D, m.τ, k₁, k₂, k₃⟩ m.θ ∈ Swing.family.den s) := by
  unfold powerlib.TMIO.Statement
  have hfield : m.field = Swing.Model.field ⟨⟨m.M, m.D, m.τ, k₁, k₂, k₃⟩, m.θ⟩ := by
    funext z
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
    · simp [Model.field, field, Model.point, hω, Swing.Model.field, Swing.Model.point]
    · simp only [Model.field, field, Swing.Model.field, SwingParams.field_apply_one,
        SwingParams.accel, SwingParams.Pe, hP, PhasePlane.mk_apply_one]
      simp [Model.point, hω, Swing.Model.point]
  rw [(connection_proof% Family.mem_den), (connection_proof% Family.mem_den)]
  change s.holds (.continuous (Port.System.autonomous m.field)) ↔
    s.holds (.continuous (Port.System.autonomous _))
  rw [hfield]

/-- Through the swing hub (`Synchronous.Swing.exactUnder_locallyExponentiallyStable`): with
positive inertia, a speed-independent sinusoidal law and `ω* = 0`, a swing model is locally
exponentially stable exactly when the angle is balanced, `k₁ + k₂ sin(θ* − k₃) = τ`, with positive
damping and synchronizing coefficient `k₂ cos(θ* − k₃) > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_sinusoid
    (m : Model) (k₁ k₂ k₃ : ℝ) (hP : m.Pe = fun θ _ => k₁ + k₂ * Real.sin (θ - k₃))
    (hω : m.ω = 0) (hM : 0 < m.M) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | k₁ + k₂ * Real.sin (m.θ - k₃) = m.τ ∧ 0 < m.D ∧
        0 < k₂ * Real.cos (m.θ - k₃)}) := by
  have hr := mem_den_iff_hub_of_sinusoid m k₁ k₂ k₃ hP hω (.flow .locallyExponentiallyStable)
  have hx := Swing.exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hr hx ⊢
  rw [(connection_proof% Spectral.exactUnder_iff_forall)] at hx
  rw [hr, ← hx _ ((TMIO.mem_realize _ _ _).mpr fun q hq => by
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hM)]
  simp only [TMIO.mem_realize, Swing.family, Swing.translate, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_ofPred_eq]
  simp [Swing.Meets, SwingParams.Pe, SwingParams.syncCoeff, hM]

end powerlib.Synchronous.GeneralSwing
