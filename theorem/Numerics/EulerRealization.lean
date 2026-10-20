import theorem.Numerics.LinearSchemes
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Map.Linearization
import theorem.Stack.Implementation

/-! # The explicit Euler implementation of a model: a realization (foundation)

A family of autonomous `C¹` fields `f x`, read about the origin, and its implementation by the
explicit Euler method with a step `h`: the discrete system `z_{k+1} = z_k + h f x (z_k)` with step
length `h`, which realizes the model it is designed from (`Implementation.ofDesign`, design map
`(x, h) ↦ x`). The realization holds under a constraint, a small step: a locally exponentially
stable model has an equilibrium at the origin with a Hurwitz Jacobian `J` (converse
linearization, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`), the Euler Jacobian
`I + h J` is Schur stable for every step `h ∈ (0, h₀]` (`exists_forwardEuler_schurStable`, from
the forward Euler stability region `forwardEuler_schurStable_iff`), and a fixed point with a Schur
Jacobian is locally exponentially stable for the map
(`Map.locallyExponentiallyStable_of_schurStable`); so the implementation is locally exponentially
stable for every small step. Without the constraint the realization is not sound: Euler
multipliers outside the closed unit disk make the implementation unstable (the field `ż = −z` with
`h = 3`: the map `z ↦ −2 z`). Scaffold: `theorem/EulerDiscretization.agda`.

Scope.
* A generic template, not a model. Model layer (M): an arbitrary family `F : Family X Q n 0` of
  autonomous fields (`F.IsAutonomous f`) on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, each `f x` of class
  `C¹`, read about the origin (a family read about selected points translates its fields so that
  the points are the origin; the Euler method commutes with the translation).
* Implementation layer (I): an arbitrary type `Y` of implementations, each with a design model
  `design y` and a step `step y`; the system is the explicit Euler map `z ↦ z + h f x z`,
  `x = design y`, `h = step y`, with step length `h` (`Map.System.autonomous`), discrete time,
  exact arithmetic (no round-off), fixed step (no step-size control).
* The implementation type is a parameter, so the template states no connection of a model of its
  own: an instance fixes its implementation type (for example a structure of a design model and a
  positive step, `theorem/Synchronous/SwingEuler.lean`) and publishes the conclusions as
  connection statements.

Source: `theorem/Numerics/LinearSchemes.lean` (`forwardEulerMatrix`,
`forwardEuler_schurStable_iff`), `theorem/Dynamics/ConverseLinearization.lean`,
`theorem/Map/Linearization.lean`, `theorem/Stack/Implementation.lean`; work-sync
`theory/T-numerical-integration.md` §1.2, §1.3, §2.7 (forward Euler and its stability region
`|1 + hλ| < 1`).

Results.
* `exists_forwardEuler_schurStable` (the step threshold): a Hurwitz `A` has `h₀ > 0` with
  `I + h A` Schur stable for every `h ∈ (0, h₀]` (every eigenvalue `λ` has `Re λ < 0`, so
  `|1 + hλ|² = 1 + h (2 Re λ + h |λ|²) < 1` for small `h > 0`; finitely many eigenvalues, the roots
  of the characteristic polynomial).
* `hasFDerivAt_eulerMap`: the Euler map of a field with Jacobian `J` has Jacobian `I + h J`.

Family and connection conclusions.
* The template `Numerics.eulerFamily F f design step : Family Y Q n 0`: every implementation read
  as its Euler map; requirements and translation are those of its design model, read through the
  design (`meets y = F.meets (design y)`). `Numerics.euler F f design step`: the implementation
  layer, every Euler implementation realizing its design model
  (`Implementation.ofDesign design`).
* M–I laws, for `F.IsAutonomous f` with `C¹` fields (foundation, stated once for every instance):
  `euler_sound_small_step` (scaffold `sound-small-step`): a locally exponentially stable model has
  a step `h₀ > 0` such that its Euler implementations with a step in `(0, h₀]` are locally
  exponentially stable. `euler_certified_small_step` (scaffold `certified-small-step`): the same
  for the design of an implementation certified for local exponential stability (`certify`).
  `not_euler_realizationSoundUnder`: without a step constraint the realization of local
  exponential stability is not sound, given an implementation whose design has an equilibrium at
  the origin with a Hurwitz Jacobian `J` and whose `I + h J` has a Schur stable left inverse;
  `not_euler_realizationSoundUnder_of_neg` (`n > 0`): the field `ż = −z` with `h = 3` is such a
  witness.
-/

noncomputable section

namespace powerlib.Numerics

open Matrix LinearSystems Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The step threshold -/

/-- **Step threshold of forward Euler.** For a Hurwitz matrix `A` there is `h₀ > 0` such that
the forward Euler matrix `I + h A` is Schur stable for every step `h ∈ (0, h₀]`. -/
@[powerlib_foundation] theorem exists_forwardEuler_schurStable {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Set.Ioc (0 : ℝ) h₀, LTI.SchurStable (forwardEulerMatrix h A) := by
  classical
  set p : Polynomial ℂ := (Linear.complexify A).charpoly with hp
  have hev : ∀ᶠ (h : ℝ) in 𝓝[>] 0,
      ∀ μ ∈ p.roots.toFinset, μ.re < 0 → ‖1 + (h : ℂ) * μ‖ < 1 := by
    rw [Filter.eventually_all_finset]
    intro μ _
    by_cases hμ : μ.re < 0
    · have hlim : Tendsto (fun h : ℝ => 2 * μ.re + h * ‖μ‖ ^ 2) (𝓝 0) (𝓝 (2 * μ.re)) := by
        have hc : Continuous fun h : ℝ => 2 * μ.re + h * ‖μ‖ ^ 2 := by fun_prop
        simpa using hc.tendsto 0
      have hneg : ∀ᶠ h in 𝓝 (0 : ℝ), 2 * μ.re + h * ‖μ‖ ^ 2 < 0 :=
        hlim.eventually (gt_mem_nhds (by linarith))
      filter_upwards [nhdsWithin_le_nhds hneg, self_mem_nhdsWithin] with h hn hpos _
      have hsq : ‖1 + (h : ℂ) * μ‖ ^ 2 = 1 + h * (2 * μ.re + h * ‖μ‖ ^ 2) := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.add_im,
          Complex.one_im, Complex.im_ofReal_mul]
        ring
      have hlt : ‖1 + (h : ℂ) * μ‖ ^ 2 < 1 := by
        rw [hsq]
        have : h * (2 * μ.re + h * ‖μ‖ ^ 2) < 0 := mul_neg_of_pos_of_neg hpos hn
        linarith
      exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hlt
    · exact Eventually.of_forall fun _ h => absurd h hμ
  obtain ⟨h₀, hh₀, hP⟩ := (nhdsGT_basis_Ioc (0 : ℝ)).eventually_iff.mp hev
  refine ⟨h₀, hh₀, fun h hh => ?_⟩
  rw [forwardEuler_schurStable_iff hh.1.ne']
  intro μ v hv heig
  have hre := Linear.isHurwitz_iff_forall_eigen.mp hA μ v hv heig
  have hroot : μ ∈ p.roots.toFinset := by
    have hdet := Criteria.det_characteristicMatrix_eq_zero_of_eigenpair A hv heig
    rw [Linear.det_characteristicMatrix_eq_eval] at hdet
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    exact hdet
  exact hP hh μ hroot hre

/-! ## The Euler map -/

/-- The explicit Euler map of a field `f` with step `h`: `z ↦ z + h f z`. -/
def eulerMap (f : ℝⁿ → ℝⁿ) (h : ℝ) (z : ℝⁿ) : ℝⁿ := z + h • f z

/-- The Euler map of a field with Jacobian `J` at `z` has Jacobian `I + h J` there. -/
@[powerlib_foundation] theorem hasFDerivAt_eulerMap {f : ℝⁿ → ℝⁿ}
    {J : Matrix (Fin n) (Fin n) ℝ} {z : ℝⁿ} (hf : HasFDerivAt f (Map.op J) z) (h : ℝ) :
    HasFDerivAt (eulerMap f h) (Map.op (forwardEulerMatrix h J)) z := by
  have hd := (hasFDerivAt_id z).add (hf.const_smul h)
  rw [Map.op, forwardEulerMatrix, map_add, map_smul, map_one, ContinuousLinearMap.one_def]
  exact hd

/-! ## The implementation family -/

variable {X Y Q : Type*}

/-- The explicit Euler implementation family of a family of autonomous fields `f`, over an
implementation type `Y` whose members carry a design model `design y` and a step `step y`: every
implementation read as the Euler map of its design's field with its step, of step length its
step; requirements and translation are those of its design model. -/
def eulerFamily (F : Family X Q n 0) (f : X → ℝⁿ → ℝⁿ) (design : Y → X) (step : Y → ℝ) :
    Family Y Q n 0 where
  system y := .discrete (Map.System.autonomous (step y) (eulerMap (f (design y)) (step y)))
  meets y := F.meets (design y)
  translate := F.translate

@[powerlib_foundation] theorem eulerFamily_isAutonomousMap (F : Family X Q n 0)
    (f : X → ℝⁿ → ℝⁿ) (design : Y → X) (step : Y → ℝ) :
    (eulerFamily F f design step).IsAutonomousMap step
      fun y => eulerMap (f (design y)) (step y) :=
  fun _ => rfl

/-- The explicit Euler realization: every Euler implementation realizes its design model. -/
def euler (F : Family X Q n 0) (f : X → ℝⁿ → ℝⁿ) (design : Y → X) (step : Y → ℝ) :
    Implementation X Q Y Q n 0 n 0 :=
  { model := F, impl := eulerFamily F f design step,
    realizes := Implementation.ofDesign design }

/-! ## The realization of local exponential stability -/

variable {F : Family X Q n 0} {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {design : Y → X} {step : Y → ℝ}

/-- A `C¹` field with an equilibrium at the origin and a Hurwitz Jacobian `J` has Euler maps
locally exponentially stable at the origin for every step below a threshold. -/
private theorem exists_euler_les {g : ℝⁿ → ℝⁿ} (hC : ContDiff ℝ 1 g) (h0 : g 0 = 0)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : fderiv ℝ g 0 = Map.op J) (hA : IsHurwitz J) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Set.Ioc (0 : ℝ) h₀,
      Map.LocallyExponentiallyStable (eulerMap g h) 0 := by
  obtain ⟨h₀, hh₀, hS⟩ := exists_forwardEuler_schurStable hA
  have hd : HasFDerivAt g (Map.op J) 0 := by
    rw [← hJ]
    exact ((hC.differentiable one_ne_zero) 0).hasFDerivAt
  refine ⟨h₀, hh₀, fun h hh => ?_⟩
  exact Map.locallyExponentiallyStable_of_schurStable (hasFDerivAt_eulerMap hd h)
    (by simp [eulerMap, h0]) (hS h hh)

/-- **Small steps realize local exponential stability.** In a family of autonomous `C¹` fields, a
locally exponentially stable model has a step `h₀ > 0` such that every Euler implementation of it
with a step in `(0, h₀]` is locally exponentially stable. -/
@[powerlib_foundation] theorem euler_sound_small_step (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) {x : X} (hx : x ∈ F.den (.flow .locallyExponentiallyStable)) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y : Y, design y = x → step y ∈ Set.Ioc (0 : ℝ) h₀ →
      y ∈ (eulerFamily F f design step).den (.flow .locallyExponentiallyStable) := by
  have hles : LocallyExponentiallyStable (f x) 0 := hF.mem_den_flow.mp hx
  set J : Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (fderiv ℝ (f x) 0)
  have hJ : fderiv ℝ (f x) 0 = Map.op J :=
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _).symm
  obtain ⟨h0, hA⟩ :=
    (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian J (hC x) hJ).mp hles
  obtain ⟨h₀, hh₀, hE⟩ := exists_euler_les (hC x) h0 hJ hA
  refine ⟨h₀, hh₀, fun y hy hstep => ?_⟩
  rw [(eulerFamily_isAutonomousMap F f design step).mem_den_flow, hy]
  exact hE _ hstep

/-- **Certified implementations with a small step.** For an Euler implementation certified for
local exponential stability (every model it realizes is locally exponentially stable), every
Euler implementation of its design with a step below a threshold is locally exponentially
stable. -/
@[powerlib_foundation] theorem euler_certified_small_step (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) {y : Y}
    (hy : y ∈ TMIO.certify (euler F f design step).realizes
      ((euler F f design step).model.den (.flow .locallyExponentiallyStable))) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y' : Y, design y' = design y → step y' ∈ Set.Ioc (0 : ℝ) h₀ →
      y' ∈ (eulerFamily F f design step).den (.flow .locallyExponentiallyStable) := by
  rw [Implementation.certify_realizes_of_design (I := euler F f design step) rfl] at hy
  exact euler_sound_small_step hF hC hy

/-- **Without a step constraint the Euler realization is not sound.** An implementation whose
design has an equilibrium at the origin and a Hurwitz Jacobian `J` (so it is locally
exponentially stable) and whose Euler Jacobian `I + h J` has a Schur stable left inverse (every
Euler multiplier outside the closed unit disk) is not locally exponentially stable. -/
@[powerlib_foundation] theorem not_euler_realizationSoundUnder (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) (hn : 0 < n) (y : Y) (J B : Matrix (Fin n) (Fin n) ℝ)
    (hJ : fderiv ℝ (f (design y)) 0 = Map.op J) (h0 : f (design y) 0 = 0) (hA : IsHurwitz J)
    (hB : B * forwardEulerMatrix (step y) J = 1) (hS : LTI.SchurStable B) :
    ¬ (euler F f design step).RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable) := by
  refine Implementation.not_realizationSoundUnder_of_design (I := euler F f design step)
    (y := y) rfl ?_ ?_ ?_
  · exact hF.mem_den_flow.mpr
      (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian J (hC _) h0 hJ hA)
  · rw [TMIO.realize_empty]
    exact Set.mem_univ _
  · intro hy
    change y ∈ (eulerFamily F f design step).den _ at hy
    rw [(eulerFamily_isAutonomousMap F f design step).mem_den_flow] at hy
    have hd : HasFDerivAt (f (design y)) (Map.op J) 0 := by
      rw [← hJ]
      exact (((hC _).differentiable one_ne_zero) 0).hasFDerivAt
    have hu := Map.unstable_of_inverse_schurStable (hasFDerivAt_eulerMap hd (step y))
      (by simp [eulerMap, h0]) hB hS hn
    exact hu (Map.LocallyExponentiallyStable.lyapunovStable hy)

/-- A complex eigenvalue of a real scalar matrix `c I` is `c`. -/
private theorem eigen_smul_one {c : ℝ} {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0)
    (heig : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ = c := by
  have hmap : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).map (algebraMap ℝ ℂ) =
      (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hmap, Matrix.smul_mulVec, Matrix.one_mulVec] at heig
  have h0 : ((c : ℂ) - μ) • v = 0 := by rw [sub_smul, heig, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hv

/-- The field `ż = −z` with step `h = 3` is a witness (`n > 0`): its Euler map is `z ↦ −2 z`. An
implementation of a design with this field and this step refutes realization soundness without a
step constraint. -/
@[powerlib_foundation] theorem not_euler_realizationSoundUnder_of_neg (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) (hn : 0 < n) (y : Y) (hx : f (design y) = fun z => -z)
    (hy : step y = 3) :
    ¬ (euler F f design step).RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable) := by
  have hJ : fderiv ℝ (f (design y)) 0 = Map.op ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    have hd := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝⁿ)).const_smul (-1 : ℝ)
    have hop : Map.op ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
        (-1 : ℝ) • ContinuousLinearMap.id ℝ ℝⁿ := by
      rw [Map.op, map_smul, map_one, ContinuousLinearMap.one_def]
    rw [hx, hop, ← hd.fderiv]
    congr 1
    funext z
    simp
  have hA : IsHurwitz ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [Linear.isHurwitz_iff_forall_eigen]
    intro μ v hv heig
    rw [eigen_smul_one hv heig]
    norm_num
  have hE : forwardEulerMatrix 3 ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (-2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [forwardEulerMatrix]
    module
  have hB : ((-1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) *
      forwardEulerMatrix (step y) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
    rw [hy, hE, smul_mul_smul_comm, mul_one]
    norm_num
  have hS : LTI.SchurStable ((-1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    intro μ v hv heig
    rw [eigen_smul_one hv heig]
    norm_num
  exact not_euler_realizationSoundUnder hF hC hn y _ _ hJ (by rw [hx]; exact neg_zero) hA hB hS

end powerlib.Numerics
