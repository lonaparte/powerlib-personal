import theorem.GFM.VSMLPF
import theorem.Criteria.Routh4
import theorem.Stack.Basic
import theorem.Dynamics.Coordinates

/-! # VSM + power filter on an experimental platform: implementation and observation layers

Model boundary.
* Implementation layer (I). A platform `VSMLPF.Rig` realizes a design model `VSMLPF.Model` (the
  model layer of `theorem/GFM/VSMLPF.lean`) under one realistic constraint, an execution delay
  `τ`: the first-order equivalent of the computation delay and the PWM update. State
  `(δ, ω, P_f, θ) : Dynamics.State 4`, in this order: power angle of the commanded internal EMF
  (rad), angular-frequency deviation (rad/s), filtered active power (pu), phase angle of the EMF
  actually applied (rad). Continuous time, autonomous:
  `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin θ − P_f)`, `τ θ̇ = δ − θ`,
  with the parameters of the design (`rigField`), read about the operating point
  `(δ*, 0, P₀, δ*)` (`Rig.point`, `Rig.field`, `Flow.Property.holds_shift_iff`).
* Excluded at the implementation layer: the sampling and discretization themselves (only their
  first-order equivalent is kept), PWM harmonics, limits, tolerances of the hardware parameters
  against the design, measurement noise. Every exclusion of the design model (voltage loop, inner
  loops, PLL, network dynamics) stays excluded.
* Observation layer (O). A record `VSMLPF.Record` is the result of one identification
  experiment: intervals `[M_lo, M_hi]`, `[D_lo, D_hi]`, `[ω_lo, ω_hi]`, `[K_lo, K_hi]` for the
  inertia, damping, filter bandwidth and synchronizing coefficient `K = K₀ cos δ*`, and an upper
  bound `τ_hi` of the delay. `VSMLPF.Produces y v`: the platform runs at its balanced operating
  point, its parameters lie in the intervals and `0 < τ ≤ τ_hi`. The production relation is a
  modelling choice of the measurement (an identification whose intervals contain the true
  parameters), not a theorem; a record has no behaviour.
* Level: equilibrium and local exponential stability / instability of the operating point, from
  the platform Jacobian computed by `fderiv` and the four-state Routh–Hurwitz criterion in both
  directions (`Criteria.isHurwitz_fin_four_iff`, with the converse linearization theorem
  `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`).

Four layers. `VSMLPF.stack` is a stack of `theorem/Stack/Basic.lean`: T = the sentences,
M = `VSMLPF.family` (`theorem/GFM/VSMLPF.lean`), I = `VSMLPF.rigFamily`, O = `VSMLPF.Record`; a
platform realizes its design model (`Implementation.ofDesign Rig.design`) and may produce the
records of
`Produces`. Data-driven inference (`Stack.infer`, the whole backward traversal) is a conclusion
about the realized design models and reuses the model-layer theorems; it becomes a conclusion
about the platform (`Stack.truth`) only through realization soundness, which needs the
implementation constraint `fastLag` and so, on the record side, the delay check `LagCheck`.
Scaffold: `theorem/VSMPlatform.agda`.

Convention: active power export-positive (GFM family exception, work-sync conventions §D9).

Source: `theorem/GFM/VSMLPF.lean` (the model layer) and its work-sync notes
(`projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md`
§15–§16), read only; the delay is the standard first-order Padé / ZOH equivalent of the
computation and PWM delay, the `[0/1]` Padé approximant `e^{−sτ} ≈ 1/(1 + sτ)`; the four-layer
reading is that of `theorem/Stack/Basic.lean`.

Results.
* Static: `contDiff_rigField`, `hasFDerivAt_rigField` (the platform Jacobian `Rig.jacobian` at the
  operating point; with `K = K₀ cos δ*` its characteristic polynomial is
  `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`, `a₃ = D/M + ω_c + 1/τ`, `a₂ = D ω_c/M + (D/M + ω_c)/τ`,
  `a₁ = D ω_c/(M τ)`, `a₀ = ω_c K/(M τ)`, and `(τ M)³ (a₃ a₂ a₁ − a₁² − a₃² a₀) = Rig.H`,
  `H = c (M + τ b)(b + τ c) − τ M c² − ω_c K (M + τ b)²`, `b = M ω_c + D`, `c = D ω_c`),
  `rigField_point_eq_zero_iff` (the operating point is an equilibrium of the platform iff the design
  angle is balanced).
* Algebra behind the connection conclusions (private): `H/ω_c = M e + τ b (e − K M) +
  τ² b (D² ω_c − K M ω_c − K D)` with `e = D b − K M` (the design is fast-filter iff `e > 0`), so
  `H > 0` forces `e > 0`, `e < 0 < K` forces `H < 0`, and `fastLag` forces `H > 0`.

Family and connection conclusions.
* `VSMLPF.rigFamily : Family Rig RigRequirement 4 0`. Requirements: the lifted design
  requirements `design q` and the realistic constraints `lag` (`0 < τ`), `routh` (`0 < H`),
  `lagged` (`H < 0 ∨ K < 0`) and `fastLag` (`τ b (K M + τ (D M ω_c² + K D)) < M (D b − K M)`: the
  delay is fast against the design margin; a sufficient condition, part of no translation). The
  local sentences translate into `{design balanced, design physical, design synchronizing, lag,
  routh}`, instability into `{design balanced, design physical, lag, lagged}`, passivity into
  nothing, the remaining flow sentences into the whole, inconsistent, language
  (`rig_realize_univ`). `rig_chain_le_semantics`: every translation is sound; `rig_exact_passive`;
  `rig_exactUnder_locallyExponentiallyStable`: within a physical design and a positive delay the
  local exponential translation is exact.
* M–I (realization). `realizationSoundUnder_locallyExponentiallyStable`: within
  `{design physical, lag, fastLag}` a platform with a locally exponentially stable design is
  locally exponentially stable, by the static reduction for a design map
  `Implementation.realizationSoundUnder_of_design` (the M-layer
  `exactUnder_locallyExponentiallyStable`, the I-layer `rig_chain_le_semantics` and one algebraic
  obligation, fast filter and fast delay give `H > 0`);
  `realizationCompleteUnder_locallyExponentiallyStable`: within `{design physical, lag}`, for every
  delay, a locally exponentially stable platform has a locally exponentially stable design (a delay
  never stabilizes); `realizationExactUnder_locallyExponentiallyStable`: within
  `{design physical, lag, fastLag}` the realization is exact.
  `not_realizationSoundUnder_locallyExponentiallyStable`: without `fastLag` it is not sound
  (`slowRig`: design `M = D = ω_c = K₀ = 1`, `P₀ = δ* = 0`, `K = 1 < 2`, delay `τ = 1`, `H = −1`;
  `slowRig_design_mem_den`, `slowRig_mem_den_unstable`).
  `realizationSoundUnder_unstable`: within `{design physical, design destabilizing, lag}` a
  platform is unstable for every delay.
* T–O (data and theory). `Record.ModelCheck` (worst-corner fast filter,
  `K_hi < D_lo ω_lo + D_lo²/M_hi`), `Record.LagCheck` (worst-corner fast delay) and
  `Record.SlowCheck` (worst-corner slow filter, `D_hi ω_hi + D_hi²/M_lo < K_lo`) are static checks
  on records. `locallyExponentiallyStable_mem_infer`: a `ModelCheck` record supports local
  exponential stability of every realized model (through the organized seed,
  `Stack.mem_infer_of_organized`, and the M-layer `chain_le_semantics`);
  `mem_certified_locallyExponentiallyStable`: the record is certified for it
  (`Stack.subset_certified_iff`); `locallyExponentiallyStable_mem_truth`: with `LagCheck` the
  record is certified for the platform constraints and the sentence is true of every platform that
  may produce it (`Stack.infer_subset_truth`).
  `infer_not_truth_of_unstable_producer`: if a record passes `ModelCheck` and an unstable platform
  may produce it, its model-level inference does not hold for every producing platform.
  `unstable_mem_infer`, `unstable_mem_truth`: a `SlowCheck` record supports instability of the
  realized models and of every producing platform, whatever its delay.
  `not_mem_predicted_locallyExponentiallyStable`: a `SlowCheck` record lies outside the records
  predicted by local exponential stability of the platform (`Stack.predicted`), so it refutes that
  sentence for every producer (`Stack.refutes`).
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix
open powerlib.Dynamics (State)

namespace VSMLPF

/-- An experimental platform realizing a design model: the design and the execution delay `τ`
(the first-order equivalent of computation delay and PWM update). -/
structure Rig where
  /-- The design model. -/
  design : Model
  /-- The execution delay. -/
  τ : ℝ

namespace Rig

variable (y : Rig)

/-- `b = M ω_c + D`. -/
def b : ℝ := y.design.g.M * y.design.g.ωc + y.design.g.D

/-- `c = D ω_c`. -/
def c : ℝ := y.design.g.D * y.design.g.ωc

/-- The scaled third Hurwitz determinant of the platform,
`H = c (M + τ b)(b + τ c) − τ M c² − ω_c K (M + τ b)²`. -/
def H : ℝ :=
  y.c * (y.design.g.M + y.τ * y.b) * (y.b + y.τ * y.c) - y.τ * y.design.g.M * y.c ^ 2 -
    y.design.g.ωc * y.design.K * (y.design.g.M + y.τ * y.b) ^ 2

/-- The operating point `(δ*, 0, P₀, δ*)`. -/
def point : State 4 := WithLp.toLp 2 ![y.design.δ, 0, y.design.g.P0, y.design.δ]

/-- The platform Jacobian at the operating point. -/
def jacobian : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
    0, -y.design.g.D / y.design.g.M, -1 / y.design.g.M, 0;
    0, 0, -y.design.g.ωc, y.design.g.ωc * y.design.K;
    1 / y.τ, 0, 0, -1 / y.τ]

end Rig

/-- The platform field in the coordinates `(δ, ω, P_f, θ)`: `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`,
`Ṗ_f = ω_c (K₀ sin θ − P_f)`, `τ θ̇ = δ − θ`. -/
def rigField (y : Rig) (x : State 4) : State 4 :=
  WithLp.toLp 2 ![x 1, (y.design.g.P0 - x 2 - y.design.g.D * x 1) / y.design.g.M,
    y.design.g.ωc * (y.design.g.K0 * Real.sin (x 3) - x 2), (x 0 - x 3) / y.τ]

/-- The platform field translated so that the operating point is the origin. -/
def Rig.field (y : Rig) (z : State 4) : State 4 := rigField y (z + y.point)

/-- Static evidence on the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem contDiff_rigField (y : Rig) {k : WithTop ℕ∞} :
    ContDiff ℝ k (rigField y) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [rigField] <;> fun_prop

/-- The Jacobian of the platform at its operating point is `Rig.jacobian`. Static evidence on the
implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem hasFDerivAt_rigField (y : Rig) :
    HasFDerivAt (rigField y) (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) y.jacobian) y.point := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have hp : ∀ k : Fin 4, HasFDerivAt (fun x : State 4 => x k)
      (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : State 4 →L[ℝ] ℝ) y.point :=
    fun k => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : State 4 →L[ℝ] ℝ).hasFDerivAt
  have p3 : y.point 3 = y.design.δ := by simp [Rig.point]
  fin_cases i
  · convert hp 1 using 1
    · funext x; simp [rigField]
    · apply ContinuousLinearMap.ext; intro v
      simp [Rig.jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
  · have h := (((hasFDerivAt_const y.design.g.P0 y.point).sub (hp 2)).sub
      ((hp 1).const_mul y.design.g.D)).const_mul y.design.g.M⁻¹
    convert h using 1
    · funext x; simp [rigField, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [Rig.jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
      ring
  · have hs := (Real.hasDerivAt_sin (y.point 3)).comp_hasFDerivAt y.point (hp 3)
    have h := ((hs.const_mul y.design.g.K0).sub (hp 2)).const_mul y.design.g.ωc
    convert h using 1
    · funext x; simp [rigField]
    · apply ContinuousLinearMap.ext; intro v
      simp [Rig.jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four, p3, Model.K]
      ring
  · have h := ((hp 0).sub (hp 3)).const_mul y.τ⁻¹
    convert h using 1
    · funext x; simp [rigField, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [Rig.jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
      ring

/-- The operating point is an equilibrium of the platform exactly when the design angle is
balanced. Static evidence on the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem rigField_point_eq_zero_iff (y : Rig) (hω : y.design.g.ωc ≠ 0) :
    rigField y y.point = 0 ↔ Meets y.design .balanced := by
  show _ ↔ y.design.g.K0 * Real.sin y.design.δ = y.design.g.P0
  constructor
  · intro h
    have e := congrArg (fun z : State 4 => z 2) h
    simp only [rigField, Rig.point, PiLp.toLp_apply, PiLp.zero_apply] at e
    simp at e
    rcases e with e | e
    · exact absurd e hω
    · linarith
  · intro hb
    ext i
    fin_cases i <;> simp [rigField, Rig.point, hb]

private theorem rig_trace_jacobian (y : Rig) :
    y.jacobian.trace = -y.design.g.D / y.design.g.M - y.design.g.ωc - 1 / y.τ := by
  simp [Rig.jacobian, Matrix.trace, Fin.sum_univ_four]
  ring

private theorem rig_m2_jacobian (y : Rig) :
    Criteria.principalMinorSum2Fin4 y.jacobian =
      y.design.g.D / y.design.g.M * y.design.g.ωc + y.design.g.D / y.design.g.M / y.τ +
        y.design.g.ωc / y.τ := by
  simp [Criteria.principalMinorSum2Fin4, Rig.jacobian]
  ring

private theorem rig_m3_jacobian (y : Rig) :
    Criteria.principalMinorSum3Fin4 y.jacobian =
      -(y.design.g.D / y.design.g.M * y.design.g.ωc / y.τ) := by
  simp [Criteria.principalMinorSum3Fin4, Rig.jacobian]
  ring

private theorem rig_det_jacobian (y : Rig) :
    y.jacobian.det = y.design.g.ωc / y.design.g.M / y.τ * y.design.K := by
  rw [Criteria.det_fin_four]
  simp [Rig.jacobian]
  ring

/-- The third Hurwitz determinant of the platform Jacobian, scaled by `(M τ)³`, is `H`. -/
private theorem gap_eq (y : Rig) (hM : y.design.g.M ≠ 0) (hτ : y.τ ≠ 0) :
    (y.jacobian.trace * Criteria.principalMinorSum2Fin4 y.jacobian *
        Criteria.principalMinorSum3Fin4 y.jacobian -
      (Criteria.principalMinorSum3Fin4 y.jacobian ^ 2 + y.jacobian.trace ^ 2 * y.jacobian.det)) *
        (y.design.g.M * y.τ) ^ 3 = y.H := by
  rw [rig_trace_jacobian, rig_m2_jacobian, rig_m3_jacobian, rig_det_jacobian]
  unfold Rig.H Rig.b Rig.c
  field_simp
  ring

/-! ## The implementation family -/

/-- Requirements on platforms: the realistic constraints and the lifted design requirements. -/
inductive RigRequirement
  /-- The design model meets `q`. -/
  | design (q : Requirement)
  /-- A positive delay `0 < τ`. -/
  | lag
  /-- The four-state Routh condition of the platform, `0 < H`. -/
  | routh
  /-- A destabilizing sign of the platform: `H < 0` or `K < 0`. -/
  | lagged
  /-- The delay is fast against the design margin:
  `τ b (K M + τ (D M ω_c² + K D)) < M (D b − K M)`. -/
  | fastLag

/-- Satisfaction of a platform requirement. -/
def RigMeets (y : Rig) : RigRequirement → Prop
  | .design q => Meets y.design q
  | .lag => 0 < y.τ
  | .routh => 0 < y.H
  | .lagged => y.H < 0 ∨ y.design.K < 0
  | .fastLag => y.τ * y.b * (y.design.K * y.design.g.M +
      y.τ * (y.design.g.D * y.design.g.M * y.design.g.ωc ^ 2 + y.design.K * y.design.g.D)) <
      y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M)

/-- The translation of the sentences into platform requirements: the local ones into a balanced,
physical, synchronizing design with a positive delay and the platform Routh condition;
instability into a balanced physical design with a positive delay and a destabilizing platform
sign; passivity into nothing; the remaining sentences into the whole, inconsistent, language. -/
def rigTranslate : Sentence → Set RigRequirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable =>
      {.design .balanced, .design .physical, .design .synchronizing, .lag, .routh}
  | .flow .unstable => {.design .balanced, .design .physical, .lag, .lagged}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The platform family. -/
def rigFamily : Family Rig RigRequirement 4 0 :=
  ⟨fun y => Port.System.autonomous y.field, RigMeets, rigTranslate⟩

@[powerlib_foundation] theorem rigFamily_isAutonomous : rigFamily.IsAutonomous Rig.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

private theorem rig_mem_den_flow_iff {y : Rig} {P : Flow.Property} :
    y ∈ rigFamily.den (.flow P) ↔ P.holds (rigField y) y.point :=
  Spectral.mem_den_flow_iff_shift (f := rigField) (pt := Rig.point) rigFamily_isAutonomous

private theorem rig_les_of {y : Rig} (hp : Meets y.design .physical) (hτ : 0 < y.τ)
    (hb : Meets y.design .balanced) (hK : 0 < y.design.K) (hH : 0 < y.H) :
    LocallyExponentiallyStable (rigField y) y.point := by
  obtain ⟨hM, hD, hω⟩ := hp
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_four y.jacobian (contDiff_rigField y)
    ((rigField_point_eq_zero_iff y hω.ne').mpr hb) (hasFDerivAt_rigField y).fderiv ?_ ?_ ?_ ?_
  · rw [rig_trace_jacobian, neg_div]
    have h1 : 0 < y.design.g.D / y.design.g.M := div_pos hD hM
    have h2 : 0 < 1 / y.τ := by positivity
    linarith
  · rw [rig_m3_jacobian]
    have : 0 < y.design.g.D / y.design.g.M * y.design.g.ωc / y.τ := by positivity
    linarith
  · rw [rig_det_jacobian]
    positivity
  · have hg := gap_eq y hM.ne' hτ.ne'
    have hMτ : 0 < (y.design.g.M * y.τ) ^ 3 := by positivity
    nlinarith

private theorem rig_unstable_of {y : Rig} (hp : Meets y.design .physical) (hτ : 0 < y.τ)
    (hb : Meets y.design .balanced) (hl : y.H < 0 ∨ y.design.K < 0) :
    Unstable (rigField y) y.point := by
  obtain ⟨hM, hD, hω⟩ := hp
  have heq := (rigField_point_eq_zero_iff y hω.ne').mpr hb
  rcases hl with hH | hK
  · refine Criteria.unstable_of_jacobian_violation_fin_four y.jacobian (contDiff_rigField y) heq
      (hasFDerivAt_rigField y).fderiv (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have hg := gap_eq y hM.ne' hτ.ne'
    have hMτ : 0 < (y.design.g.M * y.τ) ^ 3 := by positivity
    nlinarith
  · refine Criteria.unstable_of_jacobian_det_neg_fin_four y.jacobian (contDiff_rigField y) heq
      (hasFDerivAt_rigField y).fderiv ?_
    rw [rig_det_jacobian]
    exact mul_neg_of_pos_of_neg (by positivity) hK

/-! ### Soundness of the platform translation -/

/-- The whole platform requirement language is inconsistent: a positive synchronizing
coefficient with the platform Routh condition has no destabilizing platform sign. -/
@[powerlib_domain] theorem rig_realize_univ :
    connection% (TMIO.realize rigFamily.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun y h => ?_
  have h1 : 0 < y.H := h .routh
  have h2 : y.H < 0 ∨ y.design.K < 0 := h .lagged
  have h3 : 0 < y.design.K := h (.design .synchronizing)
  rcases h2 with h2 | h2 <;> linarith

/-- Every translation of the platform family is sound: the four-state Routh–Hurwitz conditions of
the platform Jacobian prove the local sentences, a destabilizing platform sign proves
instability, and passivity holds without requirement. -/
@[powerlib_domain] theorem rig_chain_le_semantics :
    connection% (∀ P, rigFamily.chain P ≤ rigFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same
    (Rs := {.design .balanced, .design .physical, .design .synchronizing, .lag, .routh})
    (Ru := {.design .balanced, .design .physical, .lag, .lagged}) (fun s => ?_) rig_realize_univ
    (fun y hy => ?_) (fun y hy => ?_) rigFamily_isAutonomous.den_passive
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  · rw [TMIO.mem_realize] at hy
    exact rig_mem_den_flow_iff.mpr (rig_les_of (hy (.design .physical) (by simp))
      (hy .lag (by simp)) (hy (.design .balanced) (by simp))
      (hy (.design .synchronizing) (by simp)) (hy .routh (by simp)))
  · rw [TMIO.mem_realize] at hy
    exact rig_mem_den_flow_iff.mpr (rig_unstable_of (hy (.design .physical) (by simp))
      (hy .lag (by simp)) (hy (.design .balanced) (by simp)) (hy .lagged (by simp)))

/-- Passivity is translated exactly: a platform without ports is passive. -/
@[powerlib_domain] theorem rig_exact_passive : connection% (rigFamily.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl rigFamily_isAutonomous.den_passive

/-- Within a physical design and a positive delay, local exponential stability of the platform is
translated exactly: the operating point is locally exponentially stable exactly when the design
is balanced, `K > 0` and the platform Routh condition `H > 0` holds (converse linearization and
the four-state Routh–Hurwitz criterion, both directions). -/
@[powerlib_domain] theorem rig_exactUnder_locallyExponentiallyStable :
    connection% (rigFamily.ExactUnder {.design .physical, .lag}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_les_of_jacobian (fun y P => rig_mem_den_flow_iff)
    {.design .physical, .lag} Rig.jacobian (fun y _ hy => ?_) (fun y _ => contDiff_rigField y)
    (fun y _ => (hasFDerivAt_rigField y).fderiv) fun y hI heq hHur => ?_
  · rw [TMIO.mem_realize] at hy
    exact rig_mem_den_flow_iff.mpr (rig_les_of
      (hy (.design .physical) (by simp [rigFamily, rigTranslate]))
      (hy .lag (by simp [rigFamily, rigTranslate]))
      (hy (.design .balanced) (by simp [rigFamily, rigTranslate]))
      (hy (.design .synchronizing) (by simp [rigFamily, rigTranslate]))
      (hy .routh (by simp [rigFamily, rigTranslate])))
  rw [TMIO.mem_realize] at hI
  have hp : Meets y.design .physical := hI (.design .physical) (by simp)
  have hτ : 0 < y.τ := hI .lag (by simp)
  obtain ⟨hM, hD, hω⟩ := hp
  rw [rigField_point_eq_zero_iff y hω.ne'] at heq
  rw [Criteria.isHurwitz_fin_four_iff] at hHur
  obtain ⟨-, -, hdet, hg⟩ := hHur
  have hK : 0 < y.design.K := by
    rw [rig_det_jacobian] at hdet
    exact pos_of_mul_pos_right hdet (by positivity)
  have hH : 0 < y.H := by
    rw [← gap_eq y hM.ne' hτ.ne']
    exact mul_pos (by linarith) (by positivity)
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl | rfl | rfl | rfl)
  · exact heq
  · exact ⟨hM, hD, hω⟩
  · exact hK
  · exact hτ
  · exact hH

/-! ## The observation layer and the stack -/

/-- The record of one identification experiment: intervals for the inertia, damping, filter
bandwidth and synchronizing coefficient, and an upper bound of the delay. -/
structure Record where
  /-- Lower bound of `M`. -/
  Mlo : ℝ
  /-- Upper bound of `M`. -/
  Mhi : ℝ
  /-- Lower bound of `D`. -/
  Dlo : ℝ
  /-- Upper bound of `D`. -/
  Dhi : ℝ
  /-- Lower bound of `ω_c`. -/
  ωlo : ℝ
  /-- Upper bound of `ω_c`. -/
  ωhi : ℝ
  /-- Lower bound of `K = K₀ cos δ*`. -/
  Klo : ℝ
  /-- Upper bound of `K`. -/
  Khi : ℝ
  /-- Upper bound of the delay `τ`. -/
  τhi : ℝ

/-- The platform `y` may produce the record `v`: it runs at its balanced operating point, its
parameters lie in the identified intervals and `0 < τ ≤ τ_hi`. -/
def Produces (y : Rig) (v : Record) : Prop :=
  Meets y.design .balanced ∧
    v.Mlo ≤ y.design.g.M ∧ y.design.g.M ≤ v.Mhi ∧
    v.Dlo ≤ y.design.g.D ∧ y.design.g.D ≤ v.Dhi ∧
    v.ωlo ≤ y.design.g.ωc ∧ y.design.g.ωc ≤ v.ωhi ∧
    v.Klo ≤ y.design.K ∧ y.design.K ≤ v.Khi ∧
    0 < y.τ ∧ y.τ ≤ v.τhi

/-- The VSM four-layer stack: the sentences, the VSM + power-filter models, the platforms realizing
their design models, and the identification records they may produce. -/
def stack : Stack Model Requirement Rig RigRequirement Record 3 0 4 0 :=
  { model := family, impl := rigFamily, realizes := Implementation.ofDesign Rig.design
    produces := {p | Produces p.1 p.2} }

private theorem stack_model : stack.model = family := rfl

private theorem stack_impl : stack.impl = rigFamily := rfl

/-- A static check of a record: positive lower bounds and the fast-filter condition at the worst
corner of the intervals, `K_hi < D_lo ω_lo + D_lo²/M_hi`. -/
def Record.ModelCheck (v : Record) : Prop :=
  0 < v.Mlo ∧ 0 < v.Dlo ∧ 0 < v.ωlo ∧ 0 < v.Klo ∧ v.Khi < v.Dlo * v.ωlo + v.Dlo ^ 2 / v.Mhi

/-- A static check of the delay bound: the fast-delay condition at the worst corner,
`τ_hi (M_hi ω_hi + D_hi)(K_hi M_hi + τ_hi (D_hi M_hi ω_hi² + K_hi D_hi)) <
M_lo (D_lo (M_lo ω_lo + D_lo) − K_hi M_hi)`. -/
def Record.LagCheck (v : Record) : Prop :=
  v.τhi * (v.Mhi * v.ωhi + v.Dhi) *
      (v.Khi * v.Mhi + v.τhi * (v.Dhi * v.Mhi * v.ωhi ^ 2 + v.Khi * v.Dhi)) <
    v.Mlo * (v.Dlo * (v.Mlo * v.ωlo + v.Dlo) - v.Khi * v.Mhi)

/-- A static check of a slow filter: positive lower bounds and
`D_hi ω_hi + D_hi²/M_lo < K_lo`. -/
def Record.SlowCheck (v : Record) : Prop :=
  0 < v.Mlo ∧ 0 < v.Dlo ∧ 0 < v.ωlo ∧ v.Dhi * v.ωhi + v.Dhi ^ 2 / v.Mlo < v.Klo

/-! ### Implementation evidence (private) -/

private theorem mem_produces {y : Rig} {v : Record} : (y, v) ∈ stack.produces ↔ Produces y v :=
  Iff.rfl

private theorem mem_realizes {x : Model} {y : Rig} : (x, y) ∈ stack.realizes ↔ y.design = x :=
  Iff.rfl

/-- The worst-corner fast-filter check places every producer's design in the translation of
local exponential stability. -/
private theorem design_fast_of_modelCheck {y : Rig} {v : Record} (hv : v.ModelCheck)
    (hp : Produces y v) :
    y.design ∈ TMIO.realize Meets (translate (.flow .locallyExponentiallyStable)) := by
  obtain ⟨hMlo, hDlo, hωlo, hKlo, hchk⟩ := hv
  obtain ⟨hb, hM1, hM2, hD1, -, hω1, -, hK1, hK2, -, -⟩ := hp
  have hM : 0 < y.design.g.M := lt_of_lt_of_le hMlo hM1
  have hD : 0 < y.design.g.D := lt_of_lt_of_le hDlo hD1
  have hω : 0 < y.design.g.ωc := lt_of_lt_of_le hωlo hω1
  rw [TMIO.mem_realize]
  intro q hq
  simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact hb
  · exact ⟨hM, hD, hω⟩
  · exact lt_of_lt_of_le hKlo hK1
  · show y.design.K < y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M
    have h1 : v.Dlo * v.ωlo ≤ y.design.g.D * y.design.g.ωc :=
      mul_le_mul hD1 hω1 hωlo.le hD.le
    have h2 : v.Dlo ^ 2 / v.Mhi ≤ y.design.g.D ^ 2 / y.design.g.M :=
      div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ hDlo.le hD1 2) hM hM2
    linarith

/-- The worst-corner slow-filter check places every producer's design in the translation of
instability. -/
private theorem design_slow_of_slowCheck {y : Rig} {v : Record} (hv : v.SlowCheck)
    (hp : Produces y v) :
    y.design ∈ TMIO.realize Meets (translate (.flow .unstable)) := by
  obtain ⟨hMlo, hDlo, hωlo, hchk⟩ := hv
  obtain ⟨hb, hM1, -, hD1, hD2, hω1, hω2, hK1, -, -, -⟩ := hp
  have hM : 0 < y.design.g.M := lt_of_lt_of_le hMlo hM1
  have hD : 0 < y.design.g.D := lt_of_lt_of_le hDlo hD1
  have hω : 0 < y.design.g.ωc := lt_of_lt_of_le hωlo hω1
  rw [TMIO.mem_realize]
  intro q hq
  simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact hb
  · exact ⟨hM, hD, hω⟩
  · left
    have h1 : y.design.g.D * y.design.g.ωc ≤ v.Dhi * v.ωhi :=
      mul_le_mul hD2 hω2 hω.le (hD.le.trans hD2)
    have h2 : y.design.g.D ^ 2 / y.design.g.M ≤ v.Dhi ^ 2 / v.Mlo :=
      div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ hD.le hD2 2) hMlo hM1
    linarith

/-- Fast filter and fast delay give the platform Routh condition:
`H = ω_c ((M e − τ b (K M + τ (D M ω_c² + K D))) + τ b e (1 + τ ω_c))`, `e = D b − K M`. -/
private theorem H_pos_of_fastLag {y : Rig} (hp : Meets y.design .physical) (hτ : 0 < y.τ)
    (hK : 0 < y.design.K) (hl : RigMeets y .fastLag) : 0 < y.H := by
  obtain ⟨hM, hD, hω⟩ := hp
  have hl' : y.τ * y.b * (y.design.K * y.design.g.M +
      y.τ * (y.design.g.D * y.design.g.M * y.design.g.ωc ^ 2 + y.design.K * y.design.g.D)) <
      y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M) := hl
  have hb : 0 < y.b := by unfold Rig.b; positivity
  have hlhs : 0 < y.τ * y.b * (y.design.K * y.design.g.M +
      y.τ * (y.design.g.D * y.design.g.M * y.design.g.ωc ^ 2 + y.design.K * y.design.g.D)) := by
    positivity
  have he : 0 < y.design.g.D * y.b - y.design.K * y.design.g.M := by
    by_contra hn
    push Not at hn
    nlinarith
  have key : y.H = y.design.g.ωc *
      ((y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M) -
        y.τ * y.b * (y.design.K * y.design.g.M +
          y.τ * (y.design.g.D * y.design.g.M * y.design.g.ωc ^ 2 + y.design.K * y.design.g.D))) +
        y.τ * y.b * (y.design.g.D * y.b - y.design.K * y.design.g.M) *
          (1 + y.τ * y.design.g.ωc)) := by
    unfold Rig.H Rig.b Rig.c
    ring
  rw [key]
  have h2 : 0 ≤ y.τ * y.b * (y.design.g.D * y.b - y.design.K * y.design.g.M) *
      (1 + y.τ * y.design.g.ωc) := by positivity
  exact mul_pos hω (by linarith)

/-- A slow filter keeps the platform unstable for every delay: `H < 0`. -/
private theorem H_neg_of_slow {y : Rig} (hp : Meets y.design .physical) (hτ : 0 < y.τ)
    (hs : y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M < y.design.K) :
    y.H < 0 := by
  obtain ⟨hM, hD, hω⟩ := hp
  have hb : 0 < y.b := by unfold Rig.b; positivity
  have hs' : y.design.g.D * y.b < y.design.K * y.design.g.M := by
    have := mul_lt_mul_of_pos_right hs hM
    have e : (y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M) * y.design.g.M =
        y.design.g.D * y.b := by unfold Rig.b; field_simp
    linarith
  have hK : 0 < y.design.K := by
    have : 0 < y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M := by positivity
    linarith
  have key : y.H = y.design.g.ωc *
      (y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M) +
        y.τ * y.b * ((y.design.g.D * y.b - y.design.K * y.design.g.M) -
          y.design.K * y.design.g.M) +
        y.τ ^ 2 * y.b * (y.design.g.D ^ 2 * y.design.g.ωc -
          y.design.K * y.design.g.M * y.design.g.ωc - y.design.K * y.design.g.D)) := by
    unfold Rig.H Rig.b Rig.c
    ring
  have hD2 : y.design.g.D ^ 2 < y.design.K * y.design.g.M := by
    have : y.design.g.D ^ 2 ≤ y.design.g.D * y.b := by
      unfold Rig.b; nlinarith [mul_pos hD (mul_pos hM hω)]
    linarith
  have t1 : y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M) < 0 :=
    mul_neg_of_pos_of_neg hM (by linarith)
  have t2 : y.τ * y.b * ((y.design.g.D * y.b - y.design.K * y.design.g.M) -
      y.design.K * y.design.g.M) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
  have t3 : y.τ ^ 2 * y.b * (y.design.g.D ^ 2 * y.design.g.ωc -
      y.design.K * y.design.g.M * y.design.g.ωc - y.design.K * y.design.g.D) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
  rw [key]
  exact mul_neg_of_pos_of_neg hω (by linarith)

/-- The worst-corner delay check places every producer in the fast-delay constraint. -/
private theorem fastLag_of_lagCheck {y : Rig} {v : Record} (hv : v.ModelCheck) (hl : v.LagCheck)
    (hp : Produces y v) : RigMeets y .fastLag := by
  obtain ⟨hMlo, hDlo, hωlo, hKlo, -⟩ := hv
  obtain ⟨-, hM1, hM2, hD1, hD2, hω1, hω2, hK1, hK2, hτ, hτ2⟩ := hp
  set M := y.design.g.M
  set D := y.design.g.D
  set ω := y.design.g.ωc
  set K := y.design.K
  set τ := y.τ
  have hM : 0 < M := lt_of_lt_of_le hMlo hM1
  have hD : 0 < D := lt_of_lt_of_le hDlo hD1
  have hω : 0 < ω := lt_of_lt_of_le hωlo hω1
  have hK : 0 < K := lt_of_lt_of_le hKlo hK1
  show τ * y.b * (K * M + τ * (D * M * ω ^ 2 + K * D)) < M * (D * y.b - K * M)
  have hbdef : y.b = M * ω + D := rfl
  rw [hbdef]
  -- upper bound of the left side
  have hb1 : M * ω + D ≤ v.Mhi * v.ωhi + v.Dhi := by
    have := mul_le_mul hM2 hω2 hω.le (hM.le.trans hM2)
    linarith
  have hKM : K * M ≤ v.Khi * v.Mhi := mul_le_mul hK2 hM2 hM.le (hK.le.trans hK2)
  have hDMω : D * M * ω ^ 2 ≤ v.Dhi * v.Mhi * v.ωhi ^ 2 :=
    mul_le_mul (mul_le_mul hD2 hM2 hM.le (hD.le.trans hD2)) (pow_le_pow_left₀ hω.le hω2 2)
      (by positivity) (by have := hD.le.trans hD2; have := hM.le.trans hM2; positivity)
  have hKD : K * D ≤ v.Khi * v.Dhi := mul_le_mul hK2 hD2 hD.le (hK.le.trans hK2)
  have hinner : D * M * ω ^ 2 + K * D ≤ v.Dhi * v.Mhi * v.ωhi ^ 2 + v.Khi * v.Dhi := by
    linarith
  have hq : K * M + τ * (D * M * ω ^ 2 + K * D) ≤
      v.Khi * v.Mhi + v.τhi * (v.Dhi * v.Mhi * v.ωhi ^ 2 + v.Khi * v.Dhi) := by
    have := mul_le_mul hτ2 hinner (by positivity) (hτ.le.trans hτ2)
    linarith
  have hlhs : τ * (M * ω + D) * (K * M + τ * (D * M * ω ^ 2 + K * D)) ≤
      v.τhi * (v.Mhi * v.ωhi + v.Dhi) *
        (v.Khi * v.Mhi + v.τhi * (v.Dhi * v.Mhi * v.ωhi ^ 2 + v.Khi * v.Dhi)) :=
    mul_le_mul (mul_le_mul hτ2 hb1 (by positivity) (hτ.le.trans hτ2)) hq (by positivity)
      (by
        have := hτ.le.trans hτ2
        have : 0 ≤ v.Mhi * v.ωhi + v.Dhi := by
          linarith [hb1, show 0 < M * ω + D by positivity]
        positivity)
  have hpos : 0 < τ * (M * ω + D) * (K * M + τ * (D * M * ω ^ 2 + K * D)) := by positivity
  -- lower bound of the right side
  have he1 : v.Dlo * (v.Mlo * v.ωlo + v.Dlo) ≤ D * (M * ω + D) := by
    have := mul_le_mul hM1 hω1 hωlo.le hM.le
    exact mul_le_mul hD1 (by linarith) (by positivity) hD.le
  have helo : 0 < v.Dlo * (v.Mlo * v.ωlo + v.Dlo) - v.Khi * v.Mhi := by
    have : 0 < v.Mlo * (v.Dlo * (v.Mlo * v.ωlo + v.Dlo) - v.Khi * v.Mhi) := by
      unfold Record.LagCheck at hl
      linarith
    exact pos_of_mul_pos_right this hMlo.le
  have hrhs : v.Mlo * (v.Dlo * (v.Mlo * v.ωlo + v.Dlo) - v.Khi * v.Mhi) ≤
      M * (D * (M * ω + D) - K * M) :=
    mul_le_mul hM1 (by linarith) helo.le hM.le
  unfold Record.LagCheck at hl
  linarith

/-! ### Realization soundness (M–I) -/

/-- Implementation soundness of local exponential stability: a platform whose design is a
physical, locally exponentially stable model and whose positive delay is fast against the design
margin is locally exponentially stable. The proof is the static reduction for a design map
`Implementation.realizationSoundUnder_of_design`: the design side is the exact M-layer
translation (`exactUnder_locallyExponentiallyStable`: balanced, `K > 0`, fast filter), the platform
side the sound I-layer translation (`rig_chain_le_semantics`), and between them one algebraic
obligation, fast filter and fast delay give the platform Routh condition `H > 0`. -/
@[powerlib_domain] theorem realizationSoundUnder_locallyExponentiallyStable :
    connection% (stack.RealizationSoundUnder {.design .physical, .lag, .fastLag}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hex := exactUnder_locallyExponentiallyStable
  have hrig := rig_chain_le_semantics
  unfold powerlib.TMIO.Statement at hex hrig
  refine Implementation.realizationSoundUnder_of_design (I := stack.toImplementation) rfl
    (ΔM := {Requirement.physical}) (by rw [stack_model]; exact hex)
    (by rw [stack_impl]; exact Family.chain_le_semantics_iff.mp hrig _) (fun y hy => ?_)
    fun y hΔ hd => ?_
  · rw [stack_impl, TMIO.mem_realize] at hy
    rw [stack_model, TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact hy (.design .physical) (by simp)
  · rw [stack_model, TMIO.mem_realize] at hd
    rw [stack_impl, TMIO.mem_realize] at hΔ ⊢
    have hp : Meets y.design .physical := hΔ (.design .physical) (by simp)
    have hτ : 0 < y.τ := hΔ .lag (by simp)
    have hK : 0 < y.design.K := hd .synchronizing (by simp [family, translate])
    intro q hq
    simp only [rigFamily, rigTranslate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hd .balanced (by simp [family, translate])
    · exact hp
    · exact hK
    · exact hτ
    · exact H_pos_of_fastLag hp hτ hK (hΔ .fastLag (by simp))

/-- A slow platform: the design `M = D = ω_c = K₀ = 1`, `P₀ = 0`, `δ* = 0` (`K = 1 < 2`, locally
exponentially stable) with the delay `τ = 1` (`H = −1`). -/
def slowRig : Rig := ⟨⟨⟨1, 1, 1, 0, 1⟩, 0⟩, 1⟩

/-- The design of the slow platform is locally exponentially stable. -/
@[powerlib_domain] theorem slowRig_design_mem_den :
    connection% (slowRig.design ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_locallyExponentiallyStable _ (by norm_num [slowRig]) (by norm_num [slowRig])
    (by norm_num [slowRig]) (by simp [slowRig]) (by simp [slowRig, Model.K])
    (by norm_num [slowRig, Model.K])

/-- The slow platform is unstable: its characteristic coefficients are positive and the third
Hurwitz determinant is negative (`H = −1`). -/
@[powerlib_domain] theorem slowRig_mem_den_unstable :
    connection% (slowRig ∈ rigFamily.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine rig_mem_den_flow_iff.mpr (rig_unstable_of (by norm_num [slowRig, Meets])
    (by norm_num [slowRig]) (by simp [slowRig, Meets]) (Or.inl ?_))
  simp [Rig.H, Rig.b, Rig.c, slowRig, Model.K]
  norm_num

/-- Without the delay constraint, local exponential stability is not realized soundly: the slow
platform has a physical, locally exponentially stable design and a positive delay, and is
unstable. -/
@[powerlib_domain] theorem not_realizationSoundUnder_locallyExponentiallyStable :
    connection% (¬ stack.RealizationSoundUnder {.design .physical, .lag}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := slowRig_design_mem_den
  have hu := slowRig_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationSoundUnder_of_design (I := stack.toImplementation) rfl hd
    ?_ fun hmem => ?_
  · rw [TMIO.mem_realize]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · show Meets slowRig.design .physical
      norm_num [slowRig, Meets]
    · show 0 < slowRig.τ
      norm_num [slowRig]
  rw [stack_impl, rig_mem_den_flow_iff] at hmem
  rw [rig_mem_den_flow_iff] at hu
  exact hu (LocallyExponentiallyStable.lyapunovStable hmem)

/-- Implementation soundness of instability: a platform whose design is physical, unstable and of
destabilizing sign is unstable for every positive delay. An unbalanced design leaves the
operating point off equilibrium; a slow filter gives `H < 0`; `K < 0` gives `det < 0`. -/
@[powerlib_domain] theorem realizationSoundUnder_unstable :
    connection% (stack.RealizationSoundUnder {.design .physical, .design .destabilizing, .lag}
      (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationSoundUnder
  rintro y ⟨-, hΔ⟩
  rw [TMIO.mem_realize] at hΔ
  have hp : Meets y.design .physical := hΔ (.design .physical) (by simp)
  have hs : Meets y.design .destabilizing := hΔ (.design .destabilizing) (by simp)
  have hτ : 0 < y.τ := hΔ .lag (by simp)
  refine rig_mem_den_flow_iff.mpr ?_
  by_cases hb : Meets y.design .balanced
  · rcases hs with hs | hK
    · exact rig_unstable_of hp hτ hb (Or.inl (H_neg_of_slow hp hτ hs))
    · exact rig_unstable_of hp hτ hb (Or.inr hK)
  · exact Dynamics.unstable_of_ne_zero (contDiff_rigField y)
      fun h => hb ((rigField_point_eq_zero_iff y hp.2.2.ne').mp h)

/-! ### Data-driven and theory-driven conclusions (T–O) -/

/-- Data-driven inference through the organized seed: a record passing the worst-corner
fast-filter check supports local exponential stability of every realized model. Every possible
producer's design meets the translation of the sentence (`design_fast_of_modelCheck`), and the
M-layer translation is sound (`chain_le_semantics`). -/
@[powerlib_domain] theorem locallyExponentiallyStable_mem_infer (v : Record) (h : v.ModelCheck) :
    connection% ((.flow .locallyExponentiallyStable : Sentence) ∈ stack.infer {v}) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  unfold powerlib.TMIO.Statement at hsound
  refine stack.mem_infer_of_organized (Family.chain_le_semantics_iff.mp hsound _) ?_
  rw [Stack.mem_inferOrganized]
  intro w hw y hy x hx
  rw [Set.mem_singleton_iff] at hw
  subst hw
  rw [mem_realizes] at hx
  subst hx
  exact design_fast_of_modelCheck h (mem_produces.mp hy)

/-- Theory-driven certification: a record passing the worst-corner fast-filter check is certified
for local exponential stability (the whole-chain Galois connection). -/
@[powerlib_domain] theorem mem_certified_locallyExponentiallyStable (v : Record)
    (h : v.ModelCheck) :
    connection% (v ∈ stack.certified {.flow .locallyExponentiallyStable}) := by
  unfold powerlib.TMIO.Statement
  have hi := locallyExponentiallyStable_mem_infer v h
  unfold powerlib.TMIO.Statement at hi
  exact (stack.subset_certified_iff {v} _).mpr (Set.singleton_subset_iff.mpr hi) rfl

/-- With the delay bound checked as well, the inferred local exponential stability is true of
every platform that may produce the record (`Stack.infer_subset_truth` with
`realizationSoundUnder_locallyExponentiallyStable`). -/
@[powerlib_domain] theorem locallyExponentiallyStable_mem_truth (v : Record) (h₁ : v.ModelCheck)
    (h₂ : v.LagCheck) :
    connection% ((.flow .locallyExponentiallyStable : Sentence) ∈ stack.truth {v}) := by
  unfold powerlib.TMIO.Statement
  have hS := realizationSoundUnder_locallyExponentiallyStable
  have hi := locallyExponentiallyStable_mem_infer v h₁
  unfold powerlib.TMIO.Statement at hS hi
  refine stack.infer_subset_truth (fun w hw => (TMIO.mem_certify _ _ _).mpr fun y hy => ?_) hS hi
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hp := mem_produces.mp hy
  rw [TMIO.mem_realize]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  obtain ⟨hMlo, hDlo, hωlo, -, -⟩ := id h₁
  obtain ⟨-, hM1, -, hD1, -, hω1, -, -, -, hτ, -⟩ := id hp
  rcases hq with rfl | rfl | rfl
  · exact ⟨lt_of_lt_of_le hMlo hM1, lt_of_lt_of_le hDlo hD1, lt_of_lt_of_le hωlo hω1⟩
  · exact hτ
  · exact fastLag_of_lagCheck h₁ h₂ hp

/-- A record passing the model check supports local exponential stability of every realized model.
If an unstable platform may produce that record, this inference is not true of every producer. -/
@[powerlib_domain] theorem infer_not_truth_of_unstable_producer (v : Record) (h : v.ModelCheck)
    (y : Rig) (hp : Produces y v) (hu : y ∈ rigFamily.den (.flow .unstable)) :
    connection% ((.flow .locallyExponentiallyStable : Sentence) ∈ stack.infer {v} ∧
      (.flow .locallyExponentiallyStable : Sentence) ∉ stack.truth {v}) := by
  unfold powerlib.TMIO.Statement
  have hi := locallyExponentiallyStable_mem_infer v h
  unfold powerlib.TMIO.Statement at hi
  refine ⟨hi, fun ht => ?_⟩
  have hmem : y ∈ rigFamily.den (.flow .locallyExponentiallyStable) :=
    (stack.mem_truth).mp ht v rfl y (mem_produces.mpr hp)
  rw [rig_mem_den_flow_iff] at hmem hu
  exact hu (LocallyExponentiallyStable.lyapunovStable hmem)

/-- A record passing the worst-corner slow-filter check supports instability of every realized
model. -/
@[powerlib_domain] theorem unstable_mem_infer (v : Record) (h : v.SlowCheck) :
    connection% ((.flow .unstable : Sentence) ∈ stack.infer {v}) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  unfold powerlib.TMIO.Statement at hsound
  refine stack.mem_infer_of_organized (Family.chain_le_semantics_iff.mp hsound _) ?_
  rw [Stack.mem_inferOrganized]
  intro w hw y hy x hx
  rw [Set.mem_singleton_iff] at hw
  subst hw
  rw [mem_realizes] at hx
  subst hx
  exact design_slow_of_slowCheck h (mem_produces.mp hy)

/-- The inferred instability is true of every platform that may produce a slow-filter record,
whatever its delay (`realizationSoundUnder_unstable`). -/
@[powerlib_domain] theorem unstable_mem_truth (v : Record) (h : v.SlowCheck) :
    connection% ((.flow .unstable : Sentence) ∈ stack.truth {v}) := by
  unfold powerlib.TMIO.Statement
  have hS := realizationSoundUnder_unstable
  have hi := unstable_mem_infer v h
  unfold powerlib.TMIO.Statement at hS hi
  refine stack.infer_subset_truth (fun w hw => (TMIO.mem_certify _ _ _).mpr fun y hy => ?_) hS hi
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hp := mem_produces.mp hy
  have hd := design_slow_of_slowCheck h hp
  rw [TMIO.mem_realize] at hd ⊢
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact hd .physical (by simp [translate])
  · exact hd .destabilizing (by simp [translate])
  · exact hp.2.2.2.2.2.2.2.2.2.1

/-! ### Realization exactness and refutation -/

/-- The platform Routh condition forces the design margin `e = D b − K M > 0`: with `e ≤ 0` every
term of `H / ω_c = M e + τ b (e − K M) + τ² b (D² ω_c − K M ω_c − K D)` is nonpositive and the
second is negative. -/
private theorem margin_pos_of_H_pos {y : Rig} (hp : Meets y.design .physical) (hτ : 0 < y.τ)
    (hH : 0 < y.H) : 0 < y.design.g.D * y.b - y.design.K * y.design.g.M := by
  obtain ⟨hM, hD, hω⟩ := hp
  by_contra hn
  push Not at hn
  have hb : 0 < y.b := by unfold Rig.b; positivity
  have hDb : y.design.g.D ^ 2 < y.design.g.D * y.b := by
    unfold Rig.b; nlinarith [mul_pos hD (mul_pos hM hω)]
  have hKM : y.design.g.D ^ 2 < y.design.K * y.design.g.M := by linarith
  have hK : 0 < y.design.K := pos_of_mul_pos_left (by nlinarith [sq_nonneg y.design.g.D]) hM.le
  have key : y.H = y.design.g.ωc *
      (y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M) +
        y.τ * y.b * ((y.design.g.D * y.b - y.design.K * y.design.g.M) -
          y.design.K * y.design.g.M) +
        y.τ ^ 2 * y.b * (y.design.g.D ^ 2 * y.design.g.ωc -
          y.design.K * y.design.g.M * y.design.g.ωc - y.design.K * y.design.g.D)) := by
    unfold Rig.H Rig.b Rig.c
    ring
  have t1 : y.design.g.M * (y.design.g.D * y.b - y.design.K * y.design.g.M) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hM.le hn
  have t2 : y.τ * y.b * ((y.design.g.D * y.b - y.design.K * y.design.g.M) -
      y.design.K * y.design.g.M) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
  have t3 : y.τ ^ 2 * y.b * (y.design.g.D ^ 2 * y.design.g.ωc -
      y.design.K * y.design.g.M * y.design.g.ωc - y.design.K * y.design.g.D) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
  have : y.H < 0 := by
    rw [key]
    exact mul_neg_of_pos_of_neg hω (by linarith)
  linarith

/-- Realization completeness of local exponential stability, for every positive delay: a locally
exponentially stable platform with a physical design has a locally exponentially stable design.
The platform is balanced with `K > 0` and `H > 0` (`rig_exactUnder_locallyExponentiallyStable`),
and `H > 0` forces the fast-filter margin of the design. A delay never stabilizes. -/
@[powerlib_domain] theorem realizationCompleteUnder_locallyExponentiallyStable :
    connection% (stack.RealizationCompleteUnder {.design .physical, .lag}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rintro y ⟨hd, hΔ⟩
  rw [Implementation.certify_realizes_of_design (I := stack.toImplementation) rfl]
  have hΔ' := hΔ
  rw [TMIO.mem_realize] at hΔ'
  have hp : Meets y.design .physical := hΔ' (.design .physical) (by simp)
  have hτ : 0 < y.τ := hΔ' .lag (by simp)
  have hex := rig_exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder at hex
  have hm : y ∈ TMIO.realize rigFamily.meets
      (rigFamily.translate (.flow .locallyExponentiallyStable) ∪ {.design .physical, .lag}) := by
    rw [hex]
    exact ⟨hd, hΔ⟩
  rw [TMIO.mem_realize] at hm
  have hb : Meets y.design .balanced := hm (.design .balanced) (by simp [rigFamily, rigTranslate])
  have hK : 0 < y.design.K := hm (.design .synchronizing) (by simp [rigFamily, rigTranslate])
  have hH : 0 < y.H := hm .routh (by simp [rigFamily, rigTranslate])
  have he := margin_pos_of_H_pos hp hτ hH
  have hf : y.design.K < y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M := by
    have hM := hp.1
    have e : (y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M) * y.design.g.M =
        y.design.g.D * y.b := by unfold Rig.b; field_simp
    have : y.design.K * y.design.g.M <
        (y.design.g.D * y.design.g.ωc + y.design.g.D ^ 2 / y.design.g.M) * y.design.g.M := by
      rw [e]; linarith
    exact lt_of_mul_lt_mul_right this hM.le
  have hmem := mem_den_locallyExponentiallyStable y.design hp.1 hp.2.1 hp.2.2 hb hK hf
  unfold powerlib.TMIO.Statement at hmem
  exact hmem

/-- Within a physical design, a positive delay and the fast-delay constraint, local exponential
stability is realized exactly: the platform is locally exponentially stable exactly when its
design is (`realizationSoundUnder_locallyExponentiallyStable`,
`realizationCompleteUnder_locallyExponentiallyStable`). -/
@[powerlib_domain] theorem realizationExactUnder_locallyExponentiallyStable :
    connection% (stack.RealizationExactUnder {.design .physical, .lag, .fastLag}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hS := realizationSoundUnder_locallyExponentiallyStable
  have hC := realizationCompleteUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hS hC
  have hsub : ({.design .physical, .lag} : Set RigRequirement) ⊆
      {.design .physical, .lag, .fastLag} := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    rcases hq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  exact stack.realizationExactUnder_iff.mpr ⟨hS, hC.mono hsub⟩

/-- A slow-filter record lies outside the records predicted by local exponential stability of the
platform; by `Stack.refutes` it refutes local exponential stability for every platform that may
produce it, whatever its delay. -/
@[powerlib_domain] theorem not_mem_predicted_locallyExponentiallyStable (v : Record)
    (h : v.SlowCheck) :
    connection% (v ∉ stack.predicted (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hv
  obtain ⟨y, hy, hp⟩ := stack.mem_predicted.mp hv
  rw [stack_impl] at hy
  have ht := unstable_mem_truth v h
  unfold powerlib.TMIO.Statement at ht
  have hu : y ∈ rigFamily.den (.flow .unstable) := (stack.mem_truth).mp ht v rfl y hp
  rw [rig_mem_den_flow_iff] at hy hu
  exact hu (LocallyExponentiallyStable.lyapunovStable hy)

end VSMLPF
end powerlib.GFM

