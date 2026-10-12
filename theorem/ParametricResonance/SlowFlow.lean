import theorem.Criteria.Hurwitz2
import theorem.Periodic.LTI

/-! # The first-order 2:1 slow flow as a real two-state LTI system

Foundation layer: exact statements **inside the averaged (slow-flow) model**. Nothing here is a
Floquet stability boundary of a voltage-source converter; the passage from a converter model to
this slow flow (projection on the victim mode, averaging, truncation) is not formalized.

Model boundary. Complex slow amplitude `A(t) ∈ ℂ` of the victim mode in the frame rotating at
half the pump frequency, continuous time, constant real damping `α₀`, constant detuning
`Δ = ω_p/2 − ω_cr`, and constant complex pump coefficient `g` (in the source `g = ε 𝒢 / 2`,
`ε` the modulation depth, `𝒢` the projected pump gain):

  `Ȧ = −(α₀ + jΔ) A + g A*`   (`slowFlowField`).

In the real coordinates `(Re A, Im A)` (`toReal`, Mathlib's orthonormal basis `{1, I}` of `ℂ`
onto `ℝ² = EuclideanSpace ℝ (Fin 2)`) this is the two-state linear field
`slowFlowSystem α₀ Δ g = LinearSystems.affineLinearVectorField (slowFlowMatrix α₀ Δ g) 0` with
state matrix `!![−α₀ + Re g, Δ + Im g; −Δ + Im g, −α₀ − Re g]` (`slowFlowMatrix`).

Results.
* `toReal_slowFlowField`, `isIntegralCurveOn_slowFlow_iff`, `hasDerivAt_slowFlow_iff`: the real
  field is exactly the complex slow flow (solutions on any time set, and global solutions,
  correspond one-to-one).
* `trace_slowFlowMatrix = −2α₀`, `det_slowFlowMatrix = α₀² + Δ² − |g|²`; characteristic
  polynomial `s² + 2α₀ s + α₀² + Δ² − |g|²`, whose roots are `−α₀ ± √(|g|² − Δ²)`
  (`slowFlow_root_iff`, real when `Δ² ≤ |g|²`).
* `slowFlow_holds_iff`, `slowFlow_exponentiallyStable_iff`: every attractive sentence of the
  Flow semantics at `0` (in particular global exponential stability) holds iff `α₀ > 0` and
  `|g|² < α₀² + Δ²`; with `g = ε𝒢/2`, `ε ≥ 0`, `α₀ > 0`: iff `ε |𝒢| < 2 √(α₀² + Δ²)`
  (`slowFlow_threshold_iff`), i.e. `ε_crit = 2√(α₀² + Δ²)/|𝒢|`.
* `exp_victim_tuned`, `monodromy_victim_tuned`: at zero pump amplitude and perfect tuning
  (`ω_cr T = π`, `T = 2π/ω_p`) the victim eigenvalues `−α₀ ± jω_cr` of a constant state matrix
  give the Floquet multiplier `−e^{−α₀T}` (a real negative double multiplier, by the LTI
  spectral mapping `Periodic.monodromy_const_mulVec_eigen`).

Source: work-sync projects/vsc-parametric-oscillation/notes/theory-draft.md §2.2 (slow flow,
`ε_crit = 2√(α₀² + Δ²)/|𝒢|`); projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §5 (slow flow and leading criterion), §7 (`σ_± = −a ± h`,
multiplier `μ = −e^{−α₀T}` at `δ̂₁ = 0` with perfect tuning `ω_cr T = π`).

Architecture: the slow flow is an averaged mathematical model with no model family; all results
remain public foundation support. The former LTI-model form is replaced by the linear field on
`ℝ²` and the linear stability hub (`Criteria.holds_affine_fin_two_iff`).
-/

noncomputable section
namespace powerlib.ParametricResonance

open Matrix Complex LinearSystems

/-! ## The model -/

/-- The complex slow-flow field `A ↦ −(α₀ + jΔ) A + g A*`. -/
def slowFlowField (α₀ Δ : ℝ) (g A : ℂ) : ℂ :=
  -((α₀ : ℂ) + (Δ : ℂ) * I) * A + g * (starRingEnd ℂ) A

/-- Real state matrix of the slow flow in the coordinates `(Re A, Im A)`. -/
def slowFlowMatrix (α₀ Δ : ℝ) (g : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-α₀ + g.re, Δ + g.im; -Δ + g.im, -α₀ - g.re]

/-- The slow flow as the linear field `x ↦ M x` on `ℝ²` (equilibrium `0`). -/
def slowFlowSystem (α₀ Δ : ℝ) (g : ℂ) : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  affineLinearVectorField (slowFlowMatrix α₀ Δ g) 0

/-- Real coordinates `(Re A, Im A)` as a continuous real-linear equivalence onto `ℝ²`. -/
def toReal : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

@[simp, powerlib_foundation] theorem toReal_apply_zero (A : ℂ) : toReal A 0 = A.re := rfl

@[simp, powerlib_foundation] theorem toReal_apply_one (A : ℂ) : toReal A 1 = A.im := rfl

@[powerlib_foundation] theorem toReal_slowFlowField (α₀ Δ : ℝ) (g A : ℂ) :
    slowFlowSystem α₀ Δ g (toReal A) = toReal (slowFlowField α₀ Δ g A) := by
  ext i
  fin_cases i <;>
    simp [slowFlowSystem, Linear.affine_apply, slowFlowMatrix, slowFlowField, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] <;> ring

/-- Solutions of the real field on any time set are exactly the real coordinates of solutions of
the complex slow flow. -/
@[powerlib_foundation] theorem isIntegralCurveOn_slowFlow_iff (α₀ Δ : ℝ) (g : ℂ)
    (A : ℝ → ℂ) (s : Set ℝ) :
    IsIntegralCurveOn (fun t => toReal (A t)) (fun _ x => slowFlowSystem α₀ Δ g x) s ↔
      IsIntegralCurveOn A (fun _ z => slowFlowField α₀ Δ g z) s := by
  refine forall₂_congr fun t _ => ?_
  simp only [toReal_slowFlowField]
  constructor
  · intro h
    have h' := toReal.symm.hasFDerivAt.comp_hasDerivWithinAt t h
    simpa [Function.comp_def] using h'
  · intro h
    exact toReal.hasFDerivAt.comp_hasDerivWithinAt t h

/-- Solution segments of the real field (`IsTrajectoryOn`) are the real coordinates of
solutions of the complex slow flow on the same segment. -/
@[powerlib_foundation] theorem isTrajectoryOn_slowFlow_iff (α₀ Δ : ℝ) (g : ℂ)
    (A : ℝ → ℂ) (a b : ℝ) :
    IsTrajectoryOn (fun t => toReal (A t)) (slowFlowSystem α₀ Δ g) a b ↔
      IsIntegralCurveOn A (fun _ z => slowFlowField α₀ Δ g z) (Set.Icc a b) :=
  isIntegralCurveOn_slowFlow_iff α₀ Δ g A _

/-- Global solutions of the real field are exactly the real coordinates of global solutions of
the complex slow flow. -/
@[powerlib_foundation] theorem hasDerivAt_slowFlow_iff (α₀ Δ : ℝ) (g : ℂ) (A : ℝ → ℂ) :
    (∀ t, HasDerivAt (fun t => toReal (A t)) (slowFlowSystem α₀ Δ g (toReal (A t))) t) ↔
      ∀ t, HasDerivAt A (slowFlowField α₀ Δ g (A t)) t := by
  refine forall_congr' fun t => ?_
  rw [toReal_slowFlowField]
  constructor
  · intro h
    have h' := toReal.symm.hasFDerivAt.comp_hasDerivAt t h
    simpa [Function.comp_def] using h'
  · intro h
    exact toReal.hasFDerivAt.comp_hasDerivAt t h

/-! ## Spectrum -/

@[powerlib_foundation] theorem trace_slowFlowMatrix (α₀ Δ : ℝ) (g : ℂ) :
    (slowFlowMatrix α₀ Δ g).trace = -2 * α₀ := by
  simp [slowFlowMatrix, Matrix.trace_fin_two]; ring

@[powerlib_foundation] theorem det_slowFlowMatrix (α₀ Δ : ℝ) (g : ℂ) :
    (slowFlowMatrix α₀ Δ g).det = α₀ ^ 2 + Δ ^ 2 - ‖g‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [slowFlowMatrix, Matrix.det_fin_two]; ring

/-- Characteristic polynomial `s² + 2α₀ s + α₀² + Δ² − |g|²`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_slowFlow (α₀ Δ : ℝ) (g : ℂ) (s : ℂ) :
    (Linear.characteristicMatrix (slowFlowMatrix α₀ Δ g) s).det =
      s ^ 2 + 2 * α₀ * s + ((α₀ ^ 2 + Δ ^ 2 - ‖g‖ ^ 2 : ℝ) : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_two, trace_slowFlowMatrix, det_slowFlowMatrix]
  push_cast; ring

/-- The characteristic roots are exactly `s = −α₀ + w` with `w² = |g|² − Δ²`, i.e.
`σ_± = −α₀ ± √(|g|² − Δ²)`. -/
@[powerlib_foundation] theorem slowFlow_root_iff (α₀ Δ : ℝ) (g : ℂ) (s : ℂ) :
    (Linear.characteristicMatrix (slowFlowMatrix α₀ Δ g) s).det = 0 ↔
      (s + α₀) ^ 2 = ((‖g‖ ^ 2 - Δ ^ 2 : ℝ) : ℂ) := by
  rw [det_characteristicMatrix_slowFlow]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linear_combination h

/-- In the real-splitting regime `Δ² ≤ |g|²` both exponents `−α₀ ± √(|g|² − Δ²)` are real
characteristic roots. -/
@[powerlib_foundation] theorem slowFlow_real_roots (α₀ Δ : ℝ) (g : ℂ) (h : Δ ^ 2 ≤ ‖g‖ ^ 2) :
    (Linear.characteristicMatrix (slowFlowMatrix α₀ Δ g)
        ((-α₀ + √(‖g‖ ^ 2 - Δ ^ 2) : ℝ) : ℂ)).det = 0 ∧
      (Linear.characteristicMatrix (slowFlowMatrix α₀ Δ g)
        ((-α₀ - √(‖g‖ ^ 2 - Δ ^ 2) : ℝ) : ℂ)).det = 0 := by
  have hs : √(‖g‖ ^ 2 - Δ ^ 2) ^ 2 = ‖g‖ ^ 2 - Δ ^ 2 := Real.sq_sqrt (by linarith)
  have hs' : ((√(‖g‖ ^ 2 - Δ ^ 2) : ℝ) : ℂ) ^ 2 = ((‖g‖ ^ 2 - Δ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast hs
  constructor <;> rw [slowFlow_root_iff, ← hs'] <;> push_cast <;> ring

/-! ## Exponential stability of the slow flow -/

/-- Every attractive sentence of the Flow semantics holds for the slow flow at `0` iff `α₀ > 0`
and `|g|² < α₀² + Δ²`. -/
@[powerlib_foundation] theorem slowFlow_holds_iff (α₀ Δ : ℝ) (g : ℂ) {P : Flow.Property}
    (hP : P.Attractive) :
    P.holds (slowFlowSystem α₀ Δ g) 0 ↔ 0 < α₀ ∧ ‖g‖ ^ 2 < α₀ ^ 2 + Δ ^ 2 := by
  rw [slowFlowSystem, Criteria.holds_affine_fin_two_iff _ _ hP, trace_slowFlowMatrix,
    det_slowFlowMatrix]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The slow flow is globally exponentially stable iff `α₀ > 0` and `|g|² < α₀² + Δ²`. -/
@[powerlib_foundation] theorem slowFlow_exponentiallyStable_iff (α₀ Δ : ℝ) (g : ℂ) :
    Flow.GloballyExponentiallyStable (slowFlowSystem α₀ Δ g) 0 ↔
      0 < α₀ ∧ ‖g‖ ^ 2 < α₀ ^ 2 + Δ ^ 2 :=
  slowFlow_holds_iff α₀ Δ g Flow.Property.attractive_globallyExponentiallyStable

/-- Leading-order threshold: with `g = ε 𝒢 / 2`, `ε ≥ 0` and `α₀ > 0`, the slow flow is
exponentially stable iff `ε |𝒢| < 2 √(α₀² + Δ²)`. -/
@[powerlib_foundation] theorem slowFlow_threshold_iff {α₀ Δ ε : ℝ} (hα : 0 < α₀) (hε : 0 ≤ ε)
    (G : ℂ) :
    Flow.GloballyExponentiallyStable (slowFlowSystem α₀ Δ ((ε : ℂ) * G / 2)) 0 ↔
      ε * ‖G‖ < 2 * √(α₀ ^ 2 + Δ ^ 2) := by
  rw [slowFlow_exponentiallyStable_iff]
  have hn : ‖(ε : ℂ) * G / 2‖ = ε * ‖G‖ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε]; simp
  rw [hn]
  have hpos : 0 ≤ ε * ‖G‖ := mul_nonneg hε (norm_nonneg G)
  have hs : 0 ≤ α₀ ^ 2 + Δ ^ 2 := by positivity
  constructor
  · rintro ⟨-, h⟩
    have : ε * ‖G‖ / 2 < √(α₀ ^ 2 + Δ ^ 2) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ ε * ‖G‖ / 2)]
      exact Real.sqrt_lt_sqrt (by positivity) h
    linarith
  · intro h
    refine ⟨hα, ?_⟩
    have h2 : ε * ‖G‖ / 2 < √(α₀ ^ 2 + Δ ^ 2) := by linarith
    have := pow_lt_pow_left₀ h2 (by positivity) (two_ne_zero)
    rwa [Real.sq_sqrt hs] at this

/-! ## Floquet multipliers at zero amplitude and perfect tuning -/

/-- With `ω T = π`, `e^{(−α₀ ± jω) T} = −e^{−α₀ T}`. -/
@[powerlib_foundation] theorem exp_victim_tuned {α₀ ω T : ℝ} (hT : ω * T = Real.pi) :
    Complex.exp ((-(α₀ : ℂ) + ω * I) * T) = -(Real.exp (-α₀ * T) : ℂ) ∧
      Complex.exp ((-(α₀ : ℂ) - ω * I) * T) = -(Real.exp (-α₀ * T) : ℂ) := by
  have e1 : (-(α₀ : ℂ) + ω * I) * T = ((-α₀ * T : ℝ) : ℂ) + (Real.pi : ℂ) * I := by
    rw [← hT]; push_cast; ring
  have e2 : (-(α₀ : ℂ) - ω * I) * T = ((-α₀ * T : ℝ) : ℂ) - (Real.pi : ℂ) * I := by
    rw [← hT]; push_cast; ring
  constructor
  · rw [e1, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_exp]; ring
  · rw [e2, Complex.exp_sub, Complex.exp_pi_mul_I, Complex.ofReal_exp]; ring

/-- Spectral mapping at zero pump amplitude: if the constant state matrix `A₀` has the victim
eigenpair `(−α₀ + jω, v)` and the pump is perfectly tuned (`ω T = π`), the monodromy matrix
`e^{T A₀}` has the real negative multiplier `−e^{−α₀ T}` on `v`. -/
@[powerlib_foundation] theorem monodromy_victim_tuned {X : Type*} [Fintype X] [DecidableEq X]
    (A₀ : Matrix X X ℝ) {α₀ ω T : ℝ} (hT0 : 0 ≤ T) (hT : ω * T = Real.pi) (s : ℝ)
    {v : X → ℂ} (hv : A₀.map (algebraMap ℝ ℂ) *ᵥ v = (-(α₀ : ℂ) + ω * I) • v) :
    (Periodic.monodromy (fun _ => A₀) T s).map (algebraMap ℝ ℂ) *ᵥ v =
      (-(Real.exp (-α₀ * T) : ℂ)) • v := by
  rw [Periodic.monodromy_const_mulVec_eigen A₀ hT0 s hv, (exp_victim_tuned hT).1]

end powerlib.ParametricResonance
