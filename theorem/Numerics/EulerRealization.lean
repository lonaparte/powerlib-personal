import theorem.TMIO.ClaimElab
import theorem.Numerics.LinearSchemes
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Map.Linearization
import theorem.Stack.Implementation

/-! # The explicit Euler implementation of a model: a realization (foundation)

A family of autonomous fields `f x`, read about the origin, and its implementation by the
explicit Euler method with a step `h`: the discrete system `z_{k+1} = z_k + h f x (z_k)` with step
length `h`, which realizes the model it is designed from (`Implementation.ofDesign`, design map
`(x, h) ↦ x`). The realization holds under a constraint, a small step: a locally exponentially
stable model whose field is `C¹` near the origin has an equilibrium there with a Hurwitz
Jacobian `J` (converse linearization for fields `C¹` on a neighbourhood of the point,
`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`), the Euler Jacobian
`I + h J` is Schur stable for every step `h ∈ (0, h₀]` (`exists_forwardEuler_schurStable`, from
the forward Euler stability region `forwardEuler_schurStable_iff`), and a fixed point with a Schur
Jacobian is locally exponentially stable for the map
(`Map.locallyExponentiallyStable_of_schurStable`); so the implementation is locally exponentially
stable for every small step. Without the constraint the realization is not sound: above a second
threshold every Euler multiplier `1 + hλ` of a Hurwitz Jacobian lies outside the closed unit disk
(`exists_forwardEuler_inverse_schurStable`), which makes the implementation unstable
(`Map.unstable_of_inverse_schurStable`; the field `ż = −z` with `h = 3`: the map `z ↦ −2 z`).
Every step uses the field only near the point (converse linearization, the Euler Jacobian at the
origin, the discrete linearization), so the laws ask smoothness of the model at hand only: `C¹`
near the origin (`ContDiffAt ℝ 1 (f x) 0`, the `_local` laws), which covers fields with a `1/V_dc`
factor near a point with `V_dc ≠ 0`, saturations near a point with headroom and arbitrary laws
that are `C¹` near the point; the laws for families whose fields are all `C¹` follow.
Scaffold: `theorem/EulerDiscretization.agda`.

Scope.
* A generic template, not a model. Model layer (M): an arbitrary family `F : Family X Q n 0` of
  autonomous fields (`F.IsAutonomous f`) on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, read about the
  origin (a family read about selected points translates its fields so that the points are the
  origin, `contDiffAt_shift`; the Euler method commutes with the translation). Smoothness: `f x`
  of class `C¹` near the origin for the model a law speaks about (the `_local` laws), or every
  `f x` of class `C¹` (the global laws).
* Implementation layer (I): an arbitrary type `Y` of implementations, each with a design model
  `design y` and a step `step y`; the system is the explicit Euler map `z ↦ z + h f x z`,
  `x = design y`, `h = step y`, with step length `h` (`Map.System.autonomous`), discrete time,
  exact arithmetic (no round-off), fixed step (no step-size control).
* The laws are connection statements about arbitrary families of `Type` (model, requirement and
  implementation types in `Type`; the definitions stay universe polymorphic). An instance fixes
  its implementation type (a structure of a design model and a positive step); the small-step
  laws of an instance are these laws applied to its family's autonomy and the public smoothness
  lemma of its field, and the instance publishes what carries its own content, a witness against
  soundness without a step constraint: `theorem/Synchronous/SwingEuler.lean` and the `Euler.lean`
  modules of `theorem/GFM/`, `theorem/GFM/Matching/`, `theorem/GFL/`, `theorem/GFL/PowerLoop/`,
  `theorem/GFL/LCLine/`, `theorem/GFL/DCLink/`, `theorem/CurrentControl/`,
  `theorem/Network/Swing/`, `theorem/Drives/`, `theorem/PLL/` and `theorem/Limiting/`.

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
* `exists_forwardEuler_inverse_schurStable` (the large-step threshold): a Hurwitz `A` has
  `h₁ > 0` with `I + h A` invertible and its inverse Schur stable for every `h ≥ h₁`
  (`|1 + hλ|² > 1` for large `h`; the inverse is the Möbius image `1 / (1 + hλ)`,
  `Linear.schurStable_mobius_iff`).
* `hasFDerivAt_eulerMap`: the Euler map of a field with Jacobian `J` has Jacobian `I + h J`.
* `contDiffAt_shift`: a field `C¹` near a point `x₀`, translated so that `x₀` is the origin, is `C¹`
  near the origin.

Family and connection conclusions.
* The template `Numerics.eulerFamily F f design step : Family Y Q n 0`: every implementation read
  as its Euler map; requirements and translation are those of its design model, read through the
  design (`meets y = F.meets (design y)`). `Numerics.euler F f design step`: the implementation
  layer, every Euler implementation realizing its design model
  (`Implementation.ofDesign design`).
* M–I laws, for `F.IsAutonomous f` (connection statements over families of `Type`, stated once
  for every instance), each with the smoothness of the model it speaks about,
  `ContDiffAt ℝ 1 (f x) 0`:
  `euler_sound_small_step_local` (scaffold `sound-small-step`): a locally exponentially stable
  model has a step `h₀ > 0` such that its Euler implementations with a step in `(0, h₀]` are
  locally exponentially stable. `euler_certified_small_step_local` (scaffold
  `certified-small-step`): the same for the design of an implementation certified for local
  exponential stability (`certify`). `not_euler_realizationSoundUnder_local`: without a step
  constraint the realization of local exponential stability is not sound, given an implementation
  whose design has an equilibrium at the origin with a Hurwitz Jacobian `J` and whose `I + h J`
  has a Schur stable left inverse; `not_euler_realizationSoundUnder_of_large_step_local` (scaffold
  `not-sound-large-step`, `n > 0`): the same from any locally exponentially stable model whose
  Euler implementations include arbitrarily large steps (the instances' form: every positive step
  is an implementation).
* The same laws for families whose fields are all `C¹` (`∀ x, ContDiff ℝ 1 (f x)`), derived from
  the local ones: `euler_sound_small_step`, `euler_certified_small_step`,
  `not_euler_realizationSoundUnder`, `not_euler_realizationSoundUnder_of_large_step`.
* `not_euler_realizationSoundUnder_of_neg` (`n > 0`, any family): an implementation of a design
  with the field `ż = −z` and step `h = 3` is a witness (the Euler map is `z ↦ −2 z`).
-/

noncomputable section

namespace powerlib.Numerics

open Matrix LinearSystems Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The step thresholds -/

/-- `|1 + hμ|² = 1 + h (2 Re μ + h |μ|²)`. -/
private theorem norm_one_add_mul_sq (h : ℝ) (μ : ℂ) :
    ‖1 + (h : ℂ) * μ‖ ^ 2 = 1 + h * (2 * μ.re + h * ‖μ‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.add_im,
    Complex.one_im, Complex.im_ofReal_mul]
  ring

/-- An eigenvalue of `A` is a root of the characteristic polynomial of its complexification. -/
private theorem mem_roots_of_eigen {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ≠ 0) (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ ∈ (Linear.complexify A).charpoly.roots.toFinset := by
  have hdet := Criteria.det_characteristicMatrix_eq_zero_of_eigenpair A hv heig
  rw [Linear.det_characteristicMatrix_eq_eval] at hdet
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
  exact hdet

/-- **Step threshold of forward Euler.** For a Hurwitz matrix `A` there is `h₀ > 0` such that
the forward Euler matrix `I + h A` is Schur stable for every step `h ∈ (0, h₀]`. -/
@[powerlib_foundation] theorem exists_forwardEuler_schurStable {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Set.Ioc (0 : ℝ) h₀, LTI.SchurStable (forwardEulerMatrix h A) := by
  classical
  have hev : ∀ᶠ (h : ℝ) in 𝓝[>] 0, ∀ μ ∈ (Linear.complexify A).charpoly.roots.toFinset,
      μ.re < 0 → ‖1 + (h : ℂ) * μ‖ < 1 := by
    rw [Filter.eventually_all_finset]
    intro μ _
    by_cases hμ : μ.re < 0
    · have hlim : Tendsto (fun h : ℝ => 2 * μ.re + h * ‖μ‖ ^ 2) (𝓝 0) (𝓝 (2 * μ.re)) := by
        have hc : Continuous fun h : ℝ => 2 * μ.re + h * ‖μ‖ ^ 2 := by fun_prop
        simpa using hc.tendsto 0
      have hneg : ∀ᶠ h in 𝓝 (0 : ℝ), 2 * μ.re + h * ‖μ‖ ^ 2 < 0 :=
        hlim.eventually (gt_mem_nhds (by linarith))
      filter_upwards [nhdsWithin_le_nhds hneg, self_mem_nhdsWithin] with h hn hpos _
      have hlt : ‖1 + (h : ℂ) * μ‖ ^ 2 < 1 := by
        rw [norm_one_add_mul_sq]
        have : h * (2 * μ.re + h * ‖μ‖ ^ 2) < 0 := mul_neg_of_pos_of_neg hpos hn
        linarith
      exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hlt
    · exact Eventually.of_forall fun _ h => absurd h hμ
  obtain ⟨h₀, hh₀, hP⟩ := (nhdsGT_basis_Ioc (0 : ℝ)).eventually_iff.mp hev
  refine ⟨h₀, hh₀, fun h hh => ?_⟩
  rw [forwardEuler_schurStable_iff hh.1.ne']
  intro μ v hv heig
  exact hP hh μ (mem_roots_of_eigen hv heig) (Linear.isHurwitz_iff_forall_eigen.mp hA μ v hv heig)

/-- A forward Euler matrix `I + h A` whose multipliers `1 + hλ` all lie outside the closed unit
disk has a Schur stable inverse (`h ≠ 0`; the Möbius image `1 / (1 + hλ)` of every eigenvalue). -/
private theorem exists_inverse_schurStable_of_forall_eigen {A : Matrix (Fin n) (Fin n) ℝ}
    {h : ℝ} (hh : h ≠ 0) (hout : ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 →
      A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v → 1 < ‖1 + (h : ℂ) * μ‖) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B * forwardEulerMatrix h A = 1 ∧ LTI.SchurStable B := by
  have hne : ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → Linear.complexify A *ᵥ v = μ • v →
      (h : ℂ) * μ + ((1 : ℝ) : ℂ) ≠ 0 := fun μ v hv heig h0 => by
    have := hout μ v hv heig
    rw [add_comm, ← Complex.ofReal_one, h0, norm_zero] at this
    exact absurd this (by norm_num)
  have hQ := Linear.isUnit_det_affine_of_forall_eigen hh hne
  have hE : forwardEulerMatrix h A = h • A + (1 : ℝ) • 1 := by
    rw [forwardEulerMatrix, one_smul, add_comm]
  refine ⟨(h • A + (1 : ℝ) • 1)⁻¹, by rw [hE]; exact Matrix.nonsing_inv_mul _ hQ, ?_⟩
  rw [Linear.schurStable_mobius_iff (α := 0) (β := 1) (by simpa using hh) hQ
    (by rw [Matrix.mul_nonsing_inv _ hQ, zero_smul, zero_add, one_smul])]
  intro μ v hv heig
  rw [norm_div, Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, norm_one,
    add_comm]
  exact (div_lt_one (by linarith [hout μ v hv heig])).mpr (hout μ v hv heig)

/-- **Large-step threshold of forward Euler.** For a Hurwitz matrix `A` there is `h₁ > 0` such
that for every step `h ≥ h₁` the forward Euler matrix `I + h A` has a Schur stable inverse: every
eigenvalue `λ` has `Re λ < 0`, so `|1 + hλ|² = 1 + h (2 Re λ + h |λ|²) > 1` for large `h`. -/
@[powerlib_foundation] theorem exists_forwardEuler_inverse_schurStable
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ ∀ h, h₁ ≤ h →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B * forwardEulerMatrix h A = 1 ∧ LTI.SchurStable B := by
  classical
  have hev : ∀ᶠ (h : ℝ) in atTop, ∀ μ ∈ (Linear.complexify A).charpoly.roots.toFinset,
      μ.re < 0 → 1 < ‖1 + (h : ℂ) * μ‖ := by
    rw [Filter.eventually_all_finset]
    intro μ _
    by_cases hμ : μ.re < 0
    · have hμ2 : 0 < ‖μ‖ ^ 2 := by
        have : μ ≠ 0 := fun h0 => by simp [h0] at hμ
        positivity
      have ht : Tendsto (fun h : ℝ => 2 * μ.re + h * ‖μ‖ ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hμ2)
      filter_upwards [ht.eventually_gt_atTop 0, eventually_gt_atTop 0] with h hc hpos _
      have hgt : 1 < ‖1 + (h : ℂ) * μ‖ ^ 2 := by
        rw [norm_one_add_mul_sq]
        nlinarith [mul_pos hpos hc]
      exact (one_lt_sq_iff₀ (norm_nonneg _)).mp hgt
    · exact Eventually.of_forall fun _ h => absurd h hμ
  obtain ⟨h₁, hP⟩ := eventually_atTop.mp hev
  refine ⟨max h₁ 1, by positivity, fun h hh => ?_⟩
  refine exists_inverse_schurStable_of_forall_eigen
    (lt_of_lt_of_le one_pos (le_of_max_le_right hh)).ne' fun μ v hv heig => ?_
  exact hP h (le_of_max_le_left hh) μ (mem_roots_of_eigen hv heig)
    (Linear.isHurwitz_iff_forall_eigen.mp hA μ v hv heig)

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

/-- A field `C¹` near a point `x₀`, translated so that `x₀` is the origin, is `C¹` near the origin:
the smoothness hypothesis of the local laws below, for a family read about selected points. -/
@[powerlib_foundation] theorem contDiffAt_shift {g : ℝⁿ → ℝⁿ} {x₀ : ℝⁿ}
    (hg : ContDiffAt ℝ 1 g x₀) : ContDiffAt ℝ 1 (fun z => g (z + x₀)) 0 :=
  ContDiffAt.comp (g := g) (f := fun z : ℝⁿ => z + x₀) 0 (by rwa [zero_add])
    (contDiffAt_id.add contDiffAt_const)

/-! ## The implementation family -/

section Template

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

end Template

/-! ## The realization of local exponential stability

The laws are connection statements about arbitrary families of `Type`. -/

variable {X Y Q : Type} {F : Family X Q n 0}
  {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {design : Y → X} {step : Y → ℝ}

/-- A field `C¹` near the origin is `C¹` on an open neighbourhood of it. -/
private theorem exists_isOpen_contDiffOn {g : ℝⁿ → ℝⁿ} (hC : ContDiffAt ℝ 1 g 0) :
    ∃ U : Set ℝⁿ, IsOpen U ∧ (0 : ℝⁿ) ∈ U ∧ ContDiffOn ℝ 1 g U := by
  obtain ⟨U, hU, h0, hCU⟩ := (hC.contDiffWithinAt (s := Set.univ)).contDiffOn' le_rfl (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hCU
  exact ⟨U, hU, h0, hCU⟩

/-- A locally exponentially stable field, `C¹` near the origin, has an equilibrium at the origin
with a Hurwitz Jacobian `J` (converse linearization for fields `C¹` on a neighbourhood,
`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`). -/
private theorem exists_isHurwitz_jacobian {g : ℝⁿ → ℝⁿ} (hC : ContDiffAt ℝ 1 g 0)
    (hles : LocallyExponentiallyStable g 0) :
    ∃ J : Matrix (Fin n) (Fin n) ℝ, fderiv ℝ g 0 = Map.op J ∧ g 0 = 0 ∧ IsHurwitz J := by
  obtain ⟨U, hU, h0, hCU⟩ := exists_isOpen_contDiffOn hC
  set J : Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (fderiv ℝ g 0)
  have hJ : fderiv ℝ g 0 = Map.op J :=
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _).symm
  exact ⟨J, hJ,
    (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local hU h0 J hCU hJ).mp hles⟩

/-- The Jacobian of a field `C¹` near the origin is its derivative there. -/
private theorem hasFDerivAt_of_fderiv_eq {g : ℝⁿ → ℝⁿ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hC : ContDiffAt ℝ 1 g 0) (hJ : fderiv ℝ g 0 = Map.op J) : HasFDerivAt g (Map.op J) 0 := by
  rw [← hJ]
  exact hC.differentiableAt_one.hasFDerivAt

/-- **Small steps realize local exponential stability, for a model `C¹` near its point.** In a
family of autonomous fields, a locally exponentially stable model whose field is `C¹` near the
origin has a step `h₀ > 0` such that every Euler implementation of it with a step in `(0, h₀]` is
locally exponentially stable. The smoothness is asked of this model only. -/
@[tmio MI]
@[powerlib_domain] theorem euler_sound_small_step_local (hF : F.IsAutonomous f) {x : X}
    (hC : ContDiffAt ℝ 1 (f x) 0) (hx : x ∈ F.den (.flow .locallyExponentiallyStable)) :
    connection% (∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y : Y, design y = x → step y ∈ Set.Ioc (0 : ℝ) h₀ →
      y ∈ (eulerFamily F f design step).den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨J, hJ, h0, hA⟩ := exists_isHurwitz_jacobian hC (hF.mem_den_flow.mp hx)
  obtain ⟨h₀, hh₀, hS⟩ := exists_forwardEuler_schurStable hA
  refine ⟨h₀, hh₀, fun y hy hstep => ?_⟩
  rw [(eulerFamily_isAutonomousMap F f design step).mem_den_flow, hy]
  exact Map.locallyExponentiallyStable_of_schurStable
    (hasFDerivAt_eulerMap (hasFDerivAt_of_fderiv_eq hC hJ) _) (by simp [eulerMap, h0]) (hS _ hstep)

/-- **Small steps realize local exponential stability.** In a family of autonomous `C¹` fields, a
locally exponentially stable model has a step `h₀ > 0` such that every Euler implementation of it
with a step in `(0, h₀]` is locally exponentially stable (`euler_sound_small_step_local`). -/
@[tmio MI]
@[powerlib_domain] theorem euler_sound_small_step (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) {x : X} (hx : x ∈ F.den (.flow .locallyExponentiallyStable)) :
    connection% (∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y : Y, design y = x → step y ∈ Set.Ioc (0 : ℝ) h₀ →
      y ∈ (eulerFamily F f design step).den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact euler_sound_small_step_local hF (hC x).contDiffAt hx

/-- **Certified implementations with a small step, for a design `C¹` near its point.** For an
Euler implementation certified for local exponential stability (every model it realizes is
locally exponentially stable) whose design has a field `C¹` near the origin, every Euler
implementation of its design with a step below a threshold is locally exponentially stable. -/
@[tmio MI]
@[powerlib_domain] theorem euler_certified_small_step_local (hF : F.IsAutonomous f) {y : Y}
    (hC : ContDiffAt ℝ 1 (f (design y)) 0)
    (hy : y ∈ TMIO.certify (euler F f design step).realizes
      ((euler F f design step).model.den (.flow .locallyExponentiallyStable))) :
    connection% (∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y' : Y, design y' = design y →
      step y' ∈ Set.Ioc (0 : ℝ) h₀ →
        y' ∈ (eulerFamily F f design step).den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [Implementation.certify_realizes_of_design (I := euler F f design step) rfl] at hy
  exact euler_sound_small_step_local hF hC hy

/-- **Certified implementations with a small step.** For an Euler implementation certified for
local exponential stability (every model it realizes is locally exponentially stable), every
Euler implementation of its design with a step below a threshold is locally exponentially
stable (`euler_certified_small_step_local`). -/
@[tmio MI]
@[powerlib_domain] theorem euler_certified_small_step (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) {y : Y}
    (hy : y ∈ TMIO.certify (euler F f design step).realizes
      ((euler F f design step).model.den (.flow .locallyExponentiallyStable))) :
    connection% (∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y' : Y, design y' = design y →
      step y' ∈ Set.Ioc (0 : ℝ) h₀ →
        y' ∈ (eulerFamily F f design step).den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact euler_certified_small_step_local hF (hC _).contDiffAt hy

/-- **Without a step constraint the Euler realization is not sound, from a design `C¹` near its
point.** An implementation whose design has a field `C¹` near the origin, an equilibrium there
and a Hurwitz Jacobian `J` (so it is locally exponentially stable) and whose Euler Jacobian
`I + h J` has a Schur stable left inverse (every Euler multiplier outside the closed unit disk) is
not locally exponentially stable. -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder_local (hF : F.IsAutonomous f)
    (hn : 0 < n) (y : Y) (J B : Matrix (Fin n) (Fin n) ℝ) (hC : ContDiffAt ℝ 1 (f (design y)) 0)
    (hJ : fderiv ℝ (f (design y)) 0 = Map.op J) (h0 : f (design y) 0 = 0) (hA : IsHurwitz J)
    (hB : B * forwardEulerMatrix (step y) J = 1) (hS : LTI.SchurStable B) :
    connection% (¬ (euler F f design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨U, hU, hU0, hCU⟩ := exists_isOpen_contDiffOn hC
  refine Implementation.not_realizationSoundUnder_of_design (I := euler F f design step)
    (y := y) rfl ?_ ?_ ?_
  · exact hF.mem_den_flow.mpr
      (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local hU hU0 J hCU h0 hJ hA)
  · rw [TMIO.realize_empty]
    exact Set.mem_univ _
  · intro hy
    change y ∈ (eulerFamily F f design step).den _ at hy
    rw [(eulerFamily_isAutonomousMap F f design step).mem_den_flow] at hy
    have hu := Map.unstable_of_inverse_schurStable
      (hasFDerivAt_eulerMap (hasFDerivAt_of_fderiv_eq hC hJ) (step y))
      (by simp [eulerMap, h0]) hB hS hn
    exact hu (Map.LocallyExponentiallyStable.lyapunovStable hy)

/-- **Without a step constraint the Euler realization is not sound.** An implementation whose
design has an equilibrium at the origin and a Hurwitz Jacobian `J` (so it is locally
exponentially stable) and whose Euler Jacobian `I + h J` has a Schur stable left inverse (every
Euler multiplier outside the closed unit disk) is not locally exponentially stable
(`not_euler_realizationSoundUnder_local`). -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder (hF : F.IsAutonomous f)
    (hC : ∀ x, ContDiff ℝ 1 (f x)) (hn : 0 < n) (y : Y) (J B : Matrix (Fin n) (Fin n) ℝ)
    (hJ : fderiv ℝ (f (design y)) 0 = Map.op J) (h0 : f (design y) 0 = 0) (hA : IsHurwitz J)
    (hB : B * forwardEulerMatrix (step y) J = 1) (hS : LTI.SchurStable B) :
    connection% (¬ (euler F f design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact not_euler_realizationSoundUnder_local hF hn y J B (hC _).contDiffAt hJ h0 hA hB hS

/-- **Large steps: without a step constraint the Euler realization is not sound, from a model
`C¹` near its point.** In a family of autonomous fields (`n > 0`), a locally exponentially stable
model whose field is `C¹` near the origin and whose Euler implementations include arbitrarily
large steps refutes realization soundness: its Jacobian `J` is Hurwitz (converse linearization),
so above a step threshold every Euler multiplier `1 + hλ` lies outside the closed unit disk
(`exists_forwardEuler_inverse_schurStable`) and that implementation is unstable. -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder_of_large_step_local
    (hF : F.IsAutonomous f) (hn : 0 < n) {x : X} (hC : ContDiffAt ℝ 1 (f x) 0)
    (hx : x ∈ F.den (.flow .locallyExponentiallyStable))
    (hY : ∀ h₁ : ℝ, ∃ y : Y, design y = x ∧ h₁ ≤ step y) :
    connection% (¬ (euler F f design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨J, hJ, h0, hA⟩ := exists_isHurwitz_jacobian hC (hF.mem_den_flow.mp hx)
  obtain ⟨h₁, -, hB⟩ := exists_forwardEuler_inverse_schurStable hA
  obtain ⟨y, rfl, hy⟩ := hY h₁
  obtain ⟨B, hB, hS⟩ := hB _ hy
  exact not_euler_realizationSoundUnder_local hF hn y J B hC hJ h0 hA hB hS

/-- **Large steps: without a step constraint the Euler realization is not sound.** In a family of
autonomous `C¹` fields (`n > 0`), a locally exponentially stable model whose Euler implementations
include arbitrarily large steps refutes realization soundness
(`not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder_of_large_step
    (hF : F.IsAutonomous f) (hC : ∀ x, ContDiff ℝ 1 (f x)) (hn : 0 < n) {x : X}
    (hx : x ∈ F.den (.flow .locallyExponentiallyStable))
    (hY : ∀ h₁ : ℝ, ∃ y : Y, design y = x ∧ h₁ ≤ step y) :
    connection% (¬ (euler F f design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact not_euler_realizationSoundUnder_of_large_step_local hF hn (hC x).contDiffAt hx hY

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
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder_of_neg (hF : F.IsAutonomous f)
    (hn : 0 < n) (y : Y) (hx : f (design y) = fun z => -z) (hy : step y = 3) :
    connection% (¬ (euler F f design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
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
  obtain ⟨B, hB, hS⟩ := exists_inverse_schurStable_of_forall_eigen (h := step y)
    (A := (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) (by rw [hy]; norm_num) fun μ v hv heig => by
      rw [eigen_smul_one hv heig, hy]
      norm_num
  have hC : ContDiffAt ℝ 1 (f (design y)) 0 := by
    rw [hx]
    exact contDiffAt_id.neg
  exact not_euler_realizationSoundUnder_local hF hn y _ B hC hJ (by rw [hx]; exact neg_zero)
    hA hB hS

end powerlib.Numerics
