import theorem.GFL.LCLine.Reduced2D
import theorem.SpecialFunctions.Sinusoid

/-! # Equilibrium count, saddle-node surface and fold of the GFL-PLL model

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/CurrentDirection.agda`.

Domain module.

Model boundary.
As in `theorem/GFL/LCLine/Reduced2D.lean` (reduced 2-state PLL model,
`y 0 = θ_e`, `y 1 = η`, frozen `i_d*, i_q*`, rigid DC, quasi-steady current loop and LC/line, no
PWM / delay / limiter, continuous time, `δω_g = 0`) and `theorem/GFL/LCLine/FullModel.lean`
(complete 10-state field). Conclusions are equilibrium-level; physical parameters with `V_g > 0`,
`ω_g C_f ≠ 0`, `Δ ≠ 0` (hence `A = V_g/√Δ > 0`), PLL gains `K_p, K_i > 0` where stated.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/equilibria-and-bifurcation.md`
§2–§4, §7; `validity-boundary.md` §8(a).

Results.
Per period window `[a, a + 2π)` of the angle `θ_e`:
* `two_equilibria_per_period` (`|c₀| < A`): exactly two equilibria `(θ_s, 0)`, `(θ_u, 0)`;
  `two_equilibria_per_period_den`: `(θ_s, 0)` is locally exponentially stable and `(θ_u, 0)` is
  unstable.
* `fold_equilibrium_per_period` (`|c₀| = A`): exactly one equilibrium; its Jacobian is the
  nonzero nilpotent `[[0, K_i], [0, 0]]` (saddle-node / fold).
* `no_equilibrium` (`|c₀| > A`): the reduced field has no equilibrium.
* `snSurface_iff` and companions: `|c₀| = A ⇔ [Δ i_d* − ((1 − b) i_d* + a i_q*)]² =
  (ω_g C_f V_g)² Δ` (IN-positive references; the square is the same for the source's
  `i*_out = −i*`), and the corresponding strict inequalities.
* `field10_exists_equilibrium_iff`: the complete 10-state field has an equilibrium iff `|c₀| ≤ A`.

Family and connection conclusions.
No new family: the stability conclusions are connection
memberships of the reduced model's members `p.pllModel θ` of the PI-PLL family
`PLL.PIPLL.family` (`theorem/GFL/LCLine/Reduced2D.lean`): `two_equilibria_per_period_den` (the
stable root is locally exponentially stable, the saddle root unstable). The count and the explicit
pair (`two_equilibria_per_period`), the fold Jacobian (`fold_equilibrium_per_period`), the absence
of equilibria (`no_equilibrium`) and the existence criteria of the 10-state field
(`field10_exists_equilibrium_iff`, `field10_exists_equilibrium_iff_explicit`) are static evidence
on the model, not connection conclusions.

Correction (`equilibria-and-bifurcation.md` §2 and §7): the note allows "possibly four zeros per
period (two stable, two saddles)" because of a `2θ_e` term and says that term makes the basin width
`< π` and asymmetric. For this model `h = c₀ − A sin(θ + φ)` exactly (`Reduction.lean`), so there
are at most two equilibria per period (`ncard_equilibria_le_two`), and the stable point and its
two neighbouring saddles are at angular distance `π ∓ 2 arcsin(c₀/A)` — the basin is asymmetric
because of `c₀ ≠ 0` (the tilt), not because of a `2θ` term.
-/

noncomputable section
namespace powerlib.GFL.LCLine
open Real Set
open powerlib.Dynamics (State)
open powerlib.PLL (piPLLJacobian)
open powerlib.SpecialFunctions (sinusoidZeros stableRoot saddleRoot)

namespace Params

variable (p : Params)

@[powerlib_foundation] theorem amp_pos (hVg : 0 < p.Vg) (hΔ : p.Δ ≠ 0) : 0 < p.amp :=
  div_pos hVg (p.sqrt_Δ_pos hΔ)

/-- Zeros of `h` (equivalently, the angles of equilibria) in the window `[a, a + 2π)`. -/
def hZeros (a : ℝ) : Set ℝ := {θ | θ ∈ Ico a (a + 2 * π) ∧ p.h θ = 0}

@[powerlib_foundation] theorem hZeros_eq (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (a : ℝ) :
    p.hZeros a = sinusoidZeros p.c0 p.amp p.phase a := by
  ext θ
  simp only [hZeros, sinusoidZeros, Set.mem_ofPred_eq, p.h_eq_polar hwC hΔ]

/-- At most two equilibrium angles per period, whatever the operating point. -/
@[powerlib_foundation] theorem ncard_equilibria_le_two (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hVg : 0 < p.Vg) (a : ℝ) : (p.hZeros a).ncard ≤ 2 := by
  rw [p.hZeros_eq hwC hΔ]
  rcases lt_trichotomy |p.c0| p.amp with h | h | h
  · rw [SpecialFunctions.ncard_sinusoidZeros_of_lt h (p.amp_pos hVg hΔ)]
  · rw [SpecialFunctions.ncard_sinusoidZeros_of_eq h (p.amp_pos hVg hΔ)]; norm_num
  · rw [SpecialFunctions.sinusoidZeros_eq_empty (p.amp_pos hVg hΔ).le h]; simp

/-- A4, `|c₀| < A`: in every period window the reduced PLL model has exactly two equilibria
`(θ_s, 0)` and `(θ_u, 0)` (the count and the explicit pair).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem two_equilibria_per_period (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hVg : 0 < p.Vg) (hc : |p.c0| < p.amp) (a : ℝ) :
    (p.hZeros a).ncard = 2 ∧
      p.hZeros a = {stableRoot p.c0 p.amp p.phase a, saddleRoot p.c0 p.amp p.phase a} := by
  have hA := p.amp_pos hVg hΔ
  refine ⟨?_, ?_⟩
  · rw [p.hZeros_eq hwC hΔ]; exact SpecialFunctions.ncard_sinusoidZeros_of_lt hc hA
  · rw [p.hZeros_eq hwC hΔ]; exact SpecialFunctions.sinusoidZeros_eq hc.le hA

/-- A4, `|c₀| < A`, `K_p, K_i > 0`: of the two equilibria of every period window, `(θ_s, 0)` is
locally exponentially stable and `(θ_u, 0)` is unstable. -/
@[powerlib_domain] theorem two_equilibria_per_period_den (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hVg : 0 < p.Vg) (hKp : 0 < p.Kp) (hKi : 0 < p.Ki) (hc : |p.c0| < p.amp) (a : ℝ) :
    connection% (p.pllModel (stableRoot p.c0 p.amp p.phase a) ∈
        PLL.PIPLL.family.den (.flow .locallyExponentiallyStable) ∧
      p.pllModel (saddleRoot p.c0 p.amp p.phase a) ∈ PLL.PIPLL.family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hA := p.amp_pos hVg hΔ
  have hs := SpecialFunctions.sqrt_one_sub_sq_pos hc hA
  refine ⟨?_, ?_⟩
  · refine p.reduced_mem_den_locallyExponentiallyStable hwC hΔ hKp hKi ?_ ?_
    · rw [p.h_eq_polar hwC hΔ]; exact SpecialFunctions.stableRoot_zero hc.le hA
    · rw [SpecialFunctions.cos_stableRoot]; nlinarith
  · refine p.reduced_mem_den_unstable hwC hΔ hKi ?_ ?_
    · rw [p.h_eq_polar hwC hΔ]; exact SpecialFunctions.saddleRoot_zero hc.le hA
    · rw [SpecialFunctions.cos_saddleRoot]; nlinarith

/-- A4, `|c₀| = A` (saddle-node): exactly one equilibrium per period, at which the Jacobian is the
nonzero nilpotent `[[0, K_i], [0, 0]]`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem fold_equilibrium_per_period (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hVg : 0 < p.Vg) (hKi : p.Ki ≠ 0) (hc : |p.c0| = p.amp) (a : ℝ) :
    (p.hZeros a).ncard = 1 ∧ p.hZeros a = {stableRoot p.c0 p.amp p.phase a} ∧
      p.reducedField (PhasePlane.mk (stableRoot p.c0 p.amp p.phase a) 0) = 0 ∧
      fderiv ℝ p.reducedField (PhasePlane.mk (stableRoot p.c0 p.amp p.phase a) 0) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian p.Kp p.Ki 0) ∧
      piPLLJacobian p.Kp p.Ki 0 ≠ 0 ∧ (piPLLJacobian p.Kp p.Ki 0) ^ 2 = 0 := by
  have hA := p.amp_pos hVg hΔ
  refine ⟨?_, ?_, p.reduced_jacobian_nilpotent hwC hΔ hKi ?_ ?_⟩
  · rw [p.hZeros_eq hwC hΔ]; exact SpecialFunctions.ncard_sinusoidZeros_of_eq hc hA
  · rw [p.hZeros_eq hwC hΔ, SpecialFunctions.sinusoidZeros_eq hc.le hA,
      SpecialFunctions.stableRoot_eq_saddleRoot hc hA, Set.pair_eq_singleton]
  · rw [p.h_eq_polar hwC hΔ]; exact SpecialFunctions.stableRoot_zero hc.le hA
  · rw [SpecialFunctions.cos_stableRoot, SpecialFunctions.sqrt_one_sub_sq_eq_zero hc hA, mul_zero]

/-- A4, `|c₀| > A`: the reduced PLL model has no equilibrium (loss of synchronism).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem no_equilibrium (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg)
    (hKi : p.Ki ≠ 0) (hc : p.amp < |p.c0|) (y : State 2) : p.reducedField y ≠ 0 := by
  rw [Ne, p.reducedField_eq_zero_iff hKi, p.h_eq_polar hwC hΔ]
  exact fun h => SpecialFunctions.sinusoid_ne_zero_of_lt (p.amp_pos hVg hΔ).le hc (y 0) h.1

/-- Existence of a PLL equilibrium angle: `(∃ θ, h θ = 0) ↔ |c₀| ≤ A`. -/
@[powerlib_foundation] theorem exists_h_zero_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg) :
    (∃ θ, p.h θ = 0) ↔ |p.c0| ≤ p.amp := by
  simp only [p.h_eq_polar hwC hΔ]
  exact SpecialFunctions.exists_sinusoid_zero_iff (p.amp_pos hVg hΔ)

/-- A3 + A4: the complete 10-state field has an equilibrium iff `|c₀| ≤ A`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field10_exists_equilibrium_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0) (hKi : p.Ki ≠ 0)
    (hVg : 0 < p.Vg) : (∃ x, p.field10 x = 0) ↔ |p.c0| ≤ p.amp := by
  rw [← p.exists_h_zero_iff hwC hΔ hVg]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨θ, hθ, -⟩ := (p.field10_eq_zero_iff hLf hCf hLg hwC hΔ hKicc hKi x).mp hx
    exact ⟨θ, hθ⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨_, (p.field10_eq_zero_iff hLf hCf hLg hwC hΔ hKicc hKi _).mpr ⟨θ, hθ, rfl⟩⟩

/-! ### The saddle-node surface in explicit parameters -/

/-- `N = Δ i_d* − ((1 − b) i_d* + a i_q*)`, so that `c₀ = N/(Δ ω_g C_f)`. -/
def snNumerator : ℝ := p.Δ * p.idRef - ((1 - p.b) * p.idRef + p.a * p.iqRef)

@[powerlib_foundation] theorem c0_eq_snNumerator (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
    p.c0 = p.snNumerator / (p.Δ * p.wC) := by
  rw [c0, snNumerator]; field_simp

@[powerlib_foundation] private lemma sq_c0_mul (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
    p.c0 ^ 2 * (p.Δ ^ 2 * p.wC ^ 2) = p.snNumerator ^ 2 := by
  rw [p.c0_eq_snNumerator hwC hΔ]; field_simp

@[powerlib_foundation] private lemma sq_amp_mul (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
    p.amp ^ 2 * (p.Δ ^ 2 * p.wC ^ 2) = (p.wC * p.Vg) ^ 2 * p.Δ := by
  have hs := p.sqrt_Δ_pos hΔ
  rw [amp, div_pow, Real.sq_sqrt p.Δ_nonneg]; field_simp

@[powerlib_foundation] private lemma abs_c0_cmp (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg) :
    (|p.c0| < p.amp ↔ p.c0 ^ 2 < p.amp ^ 2) ∧ (|p.c0| = p.amp ↔ p.c0 ^ 2 = p.amp ^ 2) := by
  have hA := p.amp_pos hVg hΔ
  constructor
  · rw [← abs_of_pos hA, sq_lt_sq, abs_abs]
  · rw [sq_eq_sq_iff_abs_eq_abs, abs_of_pos hA]

/-- Saddle-node surface `Σ_SN`: `|c₀| = A ⇔ N² = (ω_g C_f V_g)² Δ`. -/
@[powerlib_foundation] theorem snSurface_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg) :
    |p.c0| = p.amp ↔ p.snNumerator ^ 2 = (p.wC * p.Vg) ^ 2 * p.Δ := by
  have hD : 0 < p.Δ ^ 2 * p.wC ^ 2 := by
    have := p.Δ_pos hΔ; positivity
  rw [(p.abs_c0_cmp hwC hΔ hVg).2, ← p.sq_c0_mul hwC hΔ, ← p.sq_amp_mul hwC hΔ]
  constructor
  · intro h; rw [h]
  · intro h; exact mul_right_cancel₀ hD.ne' h

/-- Interior of the existence region: `|c₀| < A ⇔ N² < (ω_g C_f V_g)² Δ`. -/
@[powerlib_foundation] theorem snInterior_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg) :
    |p.c0| < p.amp ↔ p.snNumerator ^ 2 < (p.wC * p.Vg) ^ 2 * p.Δ := by
  have hD : 0 < p.Δ ^ 2 * p.wC ^ 2 := by
    have := p.Δ_pos hΔ; positivity
  rw [(p.abs_c0_cmp hwC hΔ hVg).1, ← p.sq_c0_mul hwC hΔ, ← p.sq_amp_mul hwC hΔ]
  exact (mul_lt_mul_iff_left₀ hD).symm

/-- Existence of a PLL equilibrium in explicit parameters: `N² ≤ (ω_g C_f V_g)² Δ`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field10_exists_equilibrium_iff_explicit (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0)
    (hKi : p.Ki ≠ 0) (hVg : 0 < p.Vg) :
    (∃ x, p.field10 x = 0) ↔ p.snNumerator ^ 2 ≤ (p.wC * p.Vg) ^ 2 * p.Δ := by
  rw [p.field10_exists_equilibrium_iff hLf hCf hLg hwC hΔ hKicc hKi hVg, le_iff_lt_or_eq,
    le_iff_lt_or_eq, p.snInterior_iff hwC hΔ hVg, p.snSurface_iff hwC hΔ hVg]

end Params

end powerlib.GFL.LCLine
