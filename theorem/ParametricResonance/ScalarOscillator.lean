import theorem.ParametricResonance.ForcedResponse
import theorem.PhasePlane.Planar

/-! # Teaching example: the forced oscillator with quadratic stiffness

A textbook example, not a converter model: an additive drive reappears as a periodic stiffness in
the variational equation through the quadratic stiffness term.

Model boundary.
* State `y = (q, q̇) = (y 0, y 1) ∈ State 2`, constant parameters `ζ, ω₀, a`, drive amplitude `F`
  (the source's `εF`) and pump frequency `ω_p`, continuous time:
  `q̈ + 2ζω₀ q̇ + ω₀² q + a q² = F cos(ω_p t)`   (`field`, time-dependent).

Source: work-sync projects/vsc-parametric-oscillation/notes/theory-draft.md §2.1.3.

Results.
* `forcedAmplitude_oscillator`, `forced_q_solves` — first-order forced response (linear part,
  fixed equilibrium `q = 0`): with `A₀ = !![0, 1; −ω₀², −2ζω₀]`, `b = (0, F)` and
  `D = ω₀² − ω_p² + 2jζω₀ω_p ≠ 0`, the state-space amplitude is `χ = (Q, jω_p Q)` with
  `Q = F/D`, so `q₁(t) = Re(Q e^{jω_p t})` solves `q̈ + 2ζω₀q̇ + ω₀²q = F cos(ω_p t)`.
* `hasFDerivAt_field`, `jacobian_indep_of_a_zero` — variational equation: the state Jacobian of
  the full field at `(q, q̇)` is `!![0, 1; −(ω₀² + 2a q), −2ζω₀]`; along a forced orbit `q_orb(t)`
  the linearization is `ÿ + 2ζω₀ẏ + [ω₀² + 2a q_orb(t)] y = 0`: the additive drive reappears as
  a periodic stiffness `2a q_orb(t)` through the curvature `a q²` (the `D²f[χ]` channel), and it
  is absent when `a = 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance.ScalarOscillator

open Matrix Complex
open powerlib.Dynamics (State)
open powerlib.PhasePlane

/-- Linear part `A₀ = !![0, 1; −ω₀², −2ζω₀]`. -/
def linPart (ζ ω₀ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -ω₀ ^ 2, -(2 * ζ * ω₀)]

/-- Drive vector `b = (0, F)`. -/
def drive (F : ℝ) : Fin 2 → ℂ := ![0, (F : ℂ)]

/-- Denominator `D = ω₀² − ω_p² + 2jζω₀ω_p`. -/
def denom (ζ ω₀ ωp : ℝ) : ℂ := (ω₀ ^ 2 - ωp ^ 2 : ℝ) + (2 * ζ * ω₀ * ωp : ℝ) * I

/-- The full time-dependent field `(q̇, −2ζω₀q̇ − ω₀²q − aq² + F cos ω_p t)`. -/
def field (ζ ω₀ a F ωp t : ℝ) (y : State 2) : State 2 :=
  mk (y 1) (-(2 * ζ * ω₀) * y 1 - ω₀ ^ 2 * y 0 - a * y 0 ^ 2 + F * Real.cos (ωp * t))

@[powerlib_foundation] theorem det_characteristicMatrix_linPart (ζ ω₀ ωp : ℝ) :
    (Linear.characteristicMatrix (linPart ζ ω₀) ((ωp : ℂ) * I)).det = denom ζ ω₀ ωp := by
  simp only [Linear.characteristicMatrix, Matrix.det_fin_two, linPart, denom]
  simp [Matrix.sub_apply]
  ring_nf
  rw [I_sq]; ring

/-- `χ = (Q, jω_p Q)` with `Q = F / D`. -/
@[powerlib_foundation] theorem forcedAmplitude_oscillator {ζ ω₀ ωp : ℝ} (F : ℝ)
    (hD : denom ζ ω₀ ωp ≠ 0) :
    forcedAmplitude (linPart ζ ω₀) (drive F) ωp =
      ![(F : ℂ) / denom ζ ω₀ ωp, (ωp : ℂ) * I * ((F : ℂ) / denom ζ ω₀ ωp)] := by
  set M := Linear.characteristicMatrix (linPart ζ ω₀) ((ωp : ℂ) * I)
  have hdet : M.det ≠ 0 := by rw [det_characteristicMatrix_linPart]; exact hD
  have hv : M *ᵥ ![(F : ℂ) / denom ζ ω₀ ωp, (ωp : ℂ) * I * ((F : ℂ) / denom ζ ω₀ ωp)] =
      drive F := by
    ext i
    fin_cases i
    · simp [M, Linear.characteristicMatrix, linPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.sub_apply, Matrix.one_apply, drive]
    · simp [M, Linear.characteristicMatrix, linPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.sub_apply, Matrix.one_apply, drive]
      field_simp
      simp only [denom]
      push_cast
      ring_nf
      rw [I_sq]; ring
  rw [forcedAmplitude, ← hv, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- The drive term is `(0, F cos ω_p t)`. -/
@[powerlib_foundation] theorem forcing_drive (F ωp t : ℝ) :
    forcing (drive F) ωp t = PhasePlane.mk 0 (F * Real.cos (ωp * t)) := by
  ext i
  fin_cases i
  · simp [forcing, drive]
  · simp only [forcing, drive]
    simp [Complex.exp_re, Complex.mul_re]

/-- The first-order forced displacement `q₁(t) = Re(Q e^{jω_p t})` solves the linear oscillator
`q̈ + 2ζω₀ q̇ + ω₀² q = F cos(ω_p t)` (written as a first-order system for `(q₁, q̇₁)`). -/
@[powerlib_foundation] theorem forced_q_solves {ζ ω₀ ωp : ℝ} (F : ℝ) (hD : denom ζ ω₀ ωp ≠ 0)
    (t : ℝ) :
    HasDerivAt (fun s => forcedOrbit (linPart ζ ω₀) (drive F) ωp s 0)
        (forcedOrbit (linPart ζ ω₀) (drive F) ωp t 1) t ∧
      HasDerivAt (fun s => forcedOrbit (linPart ζ ω₀) (drive F) ωp s 1)
        (-(2 * ζ * ω₀) * forcedOrbit (linPart ζ ω₀) (drive F) ωp t 1 -
          ω₀ ^ 2 * forcedOrbit (linPart ζ ω₀) (drive F) ωp t 0 + F * Real.cos (ωp * t)) t ∧
      forcedOrbit (linPart ζ ω₀) (drive F) ωp t 0 =
        ((F : ℂ) / denom ζ ω₀ ωp * Complex.exp ((ωp : ℂ) * t * I)).re := by
  have hdet : (Linear.characteristicMatrix (linPart ζ ω₀) ((ωp : ℂ) * I)).det ≠ 0 := by
    rw [det_characteristicMatrix_linPart]; exact hD
  have h := forcedOrbit_solves (drive F) hdet t
  rw [Dynamics.hasDerivAt_iff_coords] at h
  refine ⟨?_, ?_, ?_⟩
  · convert h 0 using 1
    simp [forcing_drive, linPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · convert h 1 using 1
    simp [forcing_drive, linPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp only [forcedOrbit, forcedAmplitude_oscillator F hD]
    rfl

/-- State Jacobian of the full field: `!![0, 1; −(ω₀² + 2a q), −2ζω₀]`. -/
@[powerlib_foundation] theorem hasFDerivAt_field (ζ ω₀ a F ωp t : ℝ) (y : State 2) :
    HasFDerivAt (field ζ ω₀ a F ωp t)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        !![0, 1; -(ω₀ ^ 2 + 2 * a * y 0), -(2 * ζ * ω₀)]) y := by
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
    ![Dynamics.coord 1, (-(2 * ζ * ω₀)) • Dynamics.coord 1 - (ω₀ ^ 2 + 2 * a * y 0) • Dynamics.coord 0] ?_ ?_
  · intro i; fin_cases i
    · exact Dynamics.hasFDerivAt_coord 1 y
    · show HasFDerivAt (fun z => field ζ ω₀ a F ωp t z 1) _ y
      have h0 := Dynamics.hasFDerivAt_coord 0 y
      have h1 := Dynamics.hasFDerivAt_coord 1 y
      have h := ((((h1.const_smul (-(2 * ζ * ω₀))).sub (h0.const_smul (ω₀ ^ 2))).sub
        ((h0.pow 2).const_smul a)).add_const (F * Real.cos (ωp * t)))
      have hf : (fun z => field ζ ω₀ a F ωp t z 1) = fun z : State 2 =>
          (-(2 * ζ * ω₀)) • z 1 - ω₀ ^ 2 • z 0 - a • z 0 ^ 2 + F * Real.cos (ωp * t) := by
        funext z; simp [field, smul_eq_mul]
      rw [hf]
      convert h using 1
      ext v; simp; ring
  · intro i v; rw [Fin.sum_univ_two]; fin_cases i <;> simp; ring

/-- Without curvature (`a = 0`) the state Jacobian is the constant `A₀` at every state: the
additive drive produces no periodic coefficient. -/
@[powerlib_foundation] theorem jacobian_indep_of_a_zero (ζ ω₀ F ωp t : ℝ) (y : State 2) :
    fderiv ℝ (field ζ ω₀ 0 F ωp t) y =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (linPart ζ ω₀) := by
  rw [(hasFDerivAt_field ζ ω₀ 0 F ωp t y).fderiv]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [linPart]

end powerlib.ParametricResonance.ScalarOscillator
