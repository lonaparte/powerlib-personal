/-
  R2a — saddle-node of the synchronisation map (single-harmonic reduction) and its link to R2b.

  On the synchronisation manifold the PLL equilibrium map reduces (ideal-source / first-harmonic
  regime, R2c's limit) to `G(θ) = A·sin θ + B·cos θ + D`, where `D` is the bias (grid-impedance
  voltage drop vs source) and `√(A²+B²)` is the amplitude.  Equilibria are zeros of `G`.

  Fold manifold Σ₂ is `D² = A²+B²` (bias = amplitude).  We prove parametrically:

  * `amplitude_bound`            : `(A·sin θ + B·cos θ)² ≤ A²+B²`  (the amplitude is `√(A²+B²)`).
  * `sync_pos_of_bias_gt_amp`    : if `A²+B² < D²` and `D > 0` then `G > 0` everywhere — **no
                                    synchronous equilibrium** (beyond Σ₂).
  * `sync_loss_of_bias_gt_amp`   : hence (via R2b `loss_of_sync`) the angle drifts unboundedly —
                                    **loss of synchronism**, fully parametric in `A,B,D`.
  * `sync_equilibrium_of_amp_ge` : conversely if `D² ≤ A²+B²` (within Σ₂) an equilibrium exists.

  The finite-`Cf` second-harmonic correction to `G` is the (un-done) extension; this is the
  dominant single-harmonic mechanism.  No `sorry`.
-/
import GFL.LossOfSync
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace GFL

open Real

/-- The first harmonic `A·sin θ + B·cos θ` has squared amplitude `≤ A²+B²`
(`(A sinθ + B cosθ)² + (A cosθ − B sinθ)² = A²+B²`). -/
theorem amplitude_bound (A B θ : ℝ) : (A * sin θ + B * cos θ) ^ 2 ≤ A ^ 2 + B ^ 2 := by
  nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (A * cos θ - B * sin θ)]

/-- **Beyond Σ₂ ⟹ no equilibrium.**  If the bias exceeds the amplitude (`A²+B² < D²`, `D > 0`),
then `G(θ) = A·sin θ + B·cos θ + D > 0` for every `θ` — `G` has no zero, i.e. there is no
synchronous equilibrium. -/
theorem sync_pos_of_bias_gt_amp (A B D : ℝ) (hD : 0 < D) (hgt : A ^ 2 + B ^ 2 < D ^ 2) (θ : ℝ) :
    0 < A * sin θ + B * cos θ + D := by
  nlinarith [amplitude_bound A B θ, hgt, hD, sq_nonneg (A * sin θ + B * cos θ + D),
    sq_nonneg (A * sin θ + B * cos θ - D)]

/-- The sync map `θ ↦ A·sin θ + B·cos θ + D` is `2π`-periodic. -/
theorem sync_periodic (A B D : ℝ) :
    Function.Periodic (fun θ => A * sin θ + B * cos θ + D) (2 * π) := by
  intro θ
  simp only
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- **R2a ⟹ R2b — loss of synchronism beyond Σ₂.**  If the bias exceeds the amplitude
(`A²+B² < D²`, `D > 0`) then along any trajectory of the PLL integrator `η' = G(θ_e)`, with
`G(θ) = A·sin θ + B·cos θ + D`, the integrator state `η` is unbounded: the converter cannot
synchronise (no synchronous equilibrium to lock to). -/
theorem sync_loss_of_bias_gt_amp (A B D : ℝ) (hD : 0 < D) (hgt : A ^ 2 + B ^ 2 < D ^ 2)
    (η θe : ℝ → ℝ)
    (hη : ∀ t, HasDerivAt η (A * sin (θe t) + B * cos (θe t) + D) t) :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < η t := by
  refine loss_of_sync η θe (fun θ => A * sin θ + B * cos θ + D) ?_ Real.two_pi_pos
    (sync_periodic A B D) (θ₀ := 0) (sync_pos_of_bias_gt_amp A B D hD hgt 0)
    (fun θ => ne_of_gt (sync_pos_of_bias_gt_amp A B D hD hgt θ)) hη
  fun_prop

/-- **Within Σ₂ ⟹ equilibrium exists.**  If the amplitude dominates the bias (`D² ≤ A²+B²`),
the sync map `G` has a zero (a synchronous equilibrium): `A·sin θ + B·cos θ` attains `±‖(B,A)‖`,
so `G` reaches `‖(B,A)‖ + D ≥ 0` and `D − ‖(B,A)‖ ≤ 0`; the intermediate value theorem gives a
zero.  Together with `sync_pos_of_bias_gt_amp` this makes `D² = A²+B²` the fold manifold Σ₂. -/
theorem sync_equilibrium_of_amp_ge (A B D : ℝ) (hle : D ^ 2 ≤ A ^ 2 + B ^ 2) :
    ∃ θ : ℝ, A * sin θ + B * cos θ + D = 0 := by
  set z : ℂ := ⟨B, A⟩ with hz_def
  set α := Complex.arg z with hα
  have hzim : z.im = A := rfl
  have hzre : z.re = B := rfl
  have hN2 : ‖z‖ ^ 2 = A ^ 2 + B ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hz_def, Complex.normSq_mk]; ring
  -- `A·sin θ + B·cos θ` attains its maximum `‖z‖` at `α = arg z`
  have hsinα : A = ‖z‖ * sin α := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hA : A = 0 := by rw [← hzim, hz0]; rfl
      rw [hz0, norm_zero, zero_mul]; exact hA
    · have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      rw [hα, Complex.sin_arg, hzim]; field_simp
  have hcosα : B = ‖z‖ * cos α := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hB : B = 0 := by rw [← hzre, hz0]; rfl
      rw [hz0, norm_zero, zero_mul]; exact hB
    · have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      rw [hα, Complex.cos_arg hz0, hzre]; field_simp
  have hmax : A * sin α + B * cos α = ‖z‖ := by
    rw [hsinα, hcosα]; linear_combination ‖z‖ * sin_sq_add_cos_sq α
  have hDN : D ^ 2 ≤ ‖z‖ ^ 2 := by rw [hN2]; exact hle
  -- `G(α) = ‖z‖ + D ≥ 0`,  `G(α+π) = D − ‖z‖ ≤ 0`  (since `|D| ≤ ‖z‖`)
  have hGα : 0 ≤ A * sin α + B * cos α + D := by rw [hmax]; nlinarith [hDN, norm_nonneg z]
  have hGαπ : A * sin (α + π) + B * cos (α + π) + D ≤ 0 := by
    rw [Real.sin_add_pi, Real.cos_add_pi]; nlinarith [hDN, norm_nonneg z, hmax]
  have hcont : ContinuousOn (fun θ => A * sin θ + B * cos θ + D) (Set.Icc α (α + π)) :=
    (by fun_prop : Continuous fun θ => A * sin θ + B * cos θ + D).continuousOn
  obtain ⟨θ, _, hθ⟩ := intermediate_value_Icc' (le_add_of_nonneg_right Real.pi_pos.le) hcont
    (show (0 : ℝ) ∈ Set.Icc (A * sin (α + π) + B * cos (α + π) + D) (A * sin α + B * cos α + D)
      from ⟨hGαπ, hGα⟩)
  exact ⟨θ, hθ⟩

end GFL
