import theorem.WPT.Gyrator
import theorem.SpecialFunctions.ReactiveProduct

/-! # Power limits of the lossless link without a sign condition on the reactive power

Power limits of the link with lossless windings in which the bridges may run inductive or
capacitive. The series capacitor of a coil carries no real power, so the real power a bridge
delivers passes through the induced voltage `jωψ` of its coil: `Re(V_k Ī_k) = Re(jω ψ_k Ī_k)`
at every tuning, and therefore `|P| ≤ |ω| |ψ_k| |I_k|` on either side. With the bridge radii this
gives, whatever the reactive power, `|P| ≤ ρ₁ρ₂/|ωM|`, `|P| ≤ Ψ₁ ρ₂/|M|` under a primary flux limit
and `|P| ≤ Ψ₂ ρ₁/|M|` under a secondary flux limit.

The exact limit under the bridges and one flux bound, with the reactive power free in sign,
reduces to `max 4uv − r²` over `0 ≤ u ≤ U`, `0 ≤ v ≤ V`, `u + v + r ≤ K`
(`SpecialFunctions.reactiveMax`): for the primary bound `u = L₁²|I₁|²`, `v = M²|I₂|²`,
`r = 2(L₁/ω)Q`, `K = Ψ₁²`, and `4uv − r² = (4L₁²/ω²) P²`. Its four regimes are the bridge corner
with slack flux (`ρ₁ρ₂/|ωM|`), the primary-current face (`P = Ψ₁ρ₂/|M|`, capacitive), the
secondary-current face (`P = Ψ₁ρ₁/L₁`, capacitive), and the bridge corner with a binding flux,
where the capacitive reactive power exactly needed to cancel the excess flux is spent. The secondary
bound is the mirror image (`u = M²|I₁|²`, `v = L₂²|I₂|²`, `r = 2(L₂/ω)Q`). Under both bounds the
power is at most the smaller of the two limits, and exactly that limit when the optimizer of the
binding bound meets the other one.

Model boundary.
* The coil pair `w : Passive.Coupled` with lossless windings, at one angular frequency, both ports
  driven by bridge fundamentals (`CurrentLimits.Driven`), RMS phasors in sinusoidal steady state;
  the flux limits bound the fundamental flux-linkage phasors `Passive.Coupled.flux₁`, `flux₂`.
  The flux identities hold at every tuning; the bridge corollaries use the resonant tuning of
  `theorem/WPT/CurrentLimits.lean`.
* Fundamental-harmonic approximation; no sign condition on the reactive power (soft switching is
  not required). The bridge-limited output power of lossy windings is
  `theorem/WPT/LossyLimits.lean`.

Source: the coil pair of `theorem/Passive/Coupled.lean`, the two-port equations of
`theorem/WPT/CurrentLimits.lean`, the gyrator law (`CurrentLimits.currents_lossless`), the
realization of `theorem/WPT/Gyrator.lean` (`Gyrator.exists_realization`) and the optimum of
`theorem/SpecialFunctions/ReactiveProduct.lean`.

Results.
* `power₁_eq_flux` (`Re(V₁ Ī₁) = Re(jω ψ₁ Ī₁)` with a lossless primary, every tuning),
  `power₂_eq_flux` (the same on the secondary), `abs_power₁_le_flux`, `abs_power₂_le_flux`
  (`|Re(V_k Ī_k)| ≤ |ω| ‖ψ_k‖ ‖I_k‖`).
* `abs_power_le_flux₁`, `abs_power_le_flux₂` (lossless resonant link, bridges `‖V_k‖ ≤ ρ_k`, any
  reactive power: `|P| ≤ Ψ₁ ρ₂/|M|` under `‖ψ₁‖ ≤ Ψ₁`, `|P| ≤ Ψ₂ ρ₁/|M|` under `‖ψ₂‖ ≤ Ψ₂`).
* One flux bound, exact: `limit₁`, `arg₁`, `power_sq_le_limit₁`, `isGreatest_power₁` (primary);
  `limit₂`, `arg₂`, `power_sq_le_limit₂`, `isGreatest_power₂` (secondary).
* Both flux bounds: `power_sq_le_both` (`P² ≤ min(limit₁, limit₂)`), `isGreatest_power_both₁`,
  `isGreatest_power_both₂` (exact when the optimizer of one bound meets the other).
* Not covered: both bounds binding at once (neither optimizer meets the other bound), and lossy
  windings with flux bounds.
-/

noncomputable section

namespace powerlib.WPT.ReactiveLimits

open Complex ComplexConjugate CurrentLimits

variable {w : Passive.Coupled} {ω : ℝ} {V₁ V₂ I₁ I₂ : ℂ}

/-- With a lossless primary, at every tuning, the real power the primary bridge delivers passes
through the induced voltage of the coil: `Re(V₁ Ī₁) = Re(jω ψ₁ Ī₁)`. -/
@[tmio M, powerlib_domain] theorem power₁_eq_flux (hR₁ : w.primary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re = ((ω : ℂ) * I * w.flux₁ I₁ I₂ * conj I₁).re := by
  obtain ⟨h1, -⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [h1, hR₁]
  simp only [Passive.Coupled.flux₁, Passive.SeriesRLC.reactance, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- With a lossless secondary, at every tuning: `Re(V₂ Ī₂) = Re(jω ψ₂ Ī₂)`. -/
@[tmio M, powerlib_domain] theorem power₂_eq_flux (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₂ * conj I₂).re = ((ω : ℂ) * I * w.flux₂ I₁ I₂ * conj I₂).re := by
  obtain ⟨-, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [h2, hR₂]
  simp only [Passive.Coupled.flux₂, Passive.SeriesRLC.reactance, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- `|Re(V₁ Ī₁)| ≤ |ω| ‖ψ₁‖ ‖I₁‖` with a lossless primary, at every tuning. -/
@[tmio M, powerlib_domain] theorem abs_power₁_le_flux (hR₁ : w.primary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    |(V₁ * conj I₁).re| ≤ |ω| * ‖w.flux₁ I₁ I₂‖ * ‖I₁‖ := by
  rw [power₁_eq_flux hR₁ h]
  calc |((ω : ℂ) * I * w.flux₁ I₁ I₂ * conj I₁).re|
      ≤ ‖(ω : ℂ) * I * w.flux₁ I₁ I₂ * conj I₁‖ := Complex.abs_re_le_norm _
    _ = |ω| * ‖w.flux₁ I₁ I₂‖ * ‖I₁‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_conj,
        Real.norm_eq_abs, mul_one]

/-- `|Re(V₂ Ī₂)| ≤ |ω| ‖ψ₂‖ ‖I₂‖` with a lossless secondary, at every tuning. -/
@[tmio M, powerlib_domain] theorem abs_power₂_le_flux (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    |(V₂ * conj I₂).re| ≤ |ω| * ‖w.flux₂ I₁ I₂‖ * ‖I₂‖ := by
  rw [power₂_eq_flux hR₂ h]
  calc |((ω : ℂ) * I * w.flux₂ I₁ I₂ * conj I₂).re|
      ≤ ‖(ω : ℂ) * I * w.flux₂ I₁ I₂ * conj I₂‖ := Complex.abs_re_le_norm _
    _ = |ω| * ‖w.flux₂ I₁ I₂‖ * ‖I₂‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_conj,
        Real.norm_eq_abs, mul_one]

/-- The lossless resonant link under a primary flux limit, whatever the reactive power:
`|P| ≤ Ψ₁ ρ₂/|M|`. -/
@[tmio M, powerlib_domain] theorem abs_power_le_flux₁ {ρ₁ ρ₂ Ψ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : ‖w.flux₁ I₁ I₂‖ ≤ Ψ₁) :
    |(V₁ * conj I₁).re| ≤ Ψ₁ * ρ₂ / |w.M| := by
  have hω : ω ≠ 0 := left_ne_zero_of_mul hm
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  obtain ⟨ha, -⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hb := abs_power₁_le_flux hR₁ h
  have hΨ : 0 ≤ Ψ₁ := (norm_nonneg _).trans hψ
  calc |(V₁ * conj I₁).re| ≤ |ω| * ‖w.flux₁ I₁ I₂‖ * ‖I₁‖ := hb
    _ ≤ |ω| * Ψ₁ * (ρ₂ / |ω * w.M|) := by gcongr
    _ = Ψ₁ * ρ₂ / |w.M| := by
      rw [abs_mul]
      field_simp

/-- The lossless resonant link under a secondary flux limit, whatever the reactive power:
`|P| ≤ Ψ₂ ρ₁/|M|`. -/
@[tmio M, powerlib_domain] theorem abs_power_le_flux₂ {ρ₁ ρ₂ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : ‖w.flux₂ I₁ I₂‖ ≤ Ψ₂) :
    |(V₁ * conj I₁).re| ≤ Ψ₂ * ρ₁ / |w.M| := by
  have hω : ω ≠ 0 := left_ne_zero_of_mul hm
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  obtain ⟨-, hb'⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hbal := power_balance w ω h
  rw [hR₁, hR₂, zero_mul, zero_mul, add_zero] at hbal
  have hb := abs_power₂_le_flux hR₂ h
  have hΨ : 0 ≤ Ψ₂ := (norm_nonneg _).trans hψ
  have he : |(V₁ * conj I₁).re| = |(V₂ * conj I₂).re| := by
    rw [show (V₁ * conj I₁).re = -(V₂ * conj I₂).re by linarith, abs_neg]
  calc |(V₁ * conj I₁).re| = |(V₂ * conj I₂).re| := he
    _ ≤ |ω| * ‖w.flux₂ I₁ I₂‖ * ‖I₂‖ := hb
    _ ≤ |ω| * Ψ₂ * (ρ₁ / |ω * w.M|) := by gcongr
    _ = Ψ₂ * ρ₁ / |w.M| := by
      rw [abs_mul]
      field_simp

/-! ## The exact limit under one flux bound, without a sign condition on `Q` -/

/-- The squared power limit under the bridges and the primary flux bound `‖ψ₁‖² ≤ Ψ₁²`:
`ω²/(4L₁²) · reactiveMax(L₁²(ρ₂/|ωM|)², M²(ρ₁/|ωM|)², Ψ₁²)`. -/
def limit₁ (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₁ : ℝ) : ℝ :=
  ω ^ 2 / (4 * w.primary.L ^ 2) * SpecialFunctions.reactiveMax
    (w.primary.L ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψ₁ ^ 2)

/-- The squared power limit under the bridges and the secondary flux bound `‖ψ₂‖² ≤ Ψ₂²`:
`ω²/(4L₂²) · reactiveMax(M²(ρ₂/|ωM|)², L₂²(ρ₁/|ωM|)², Ψ₂²)`. -/
def limit₂ (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₂ : ℝ) : ℝ :=
  ω ^ 2 / (4 * w.secondary.L ^ 2) * SpecialFunctions.reactiveMax
    (w.M ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (w.secondary.L ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψ₂ ^ 2)

/-- The optimizer `(u, v, r)` of the primary-flux problem. -/
def arg₁ (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₁ : ℝ) : ℝ × ℝ × ℝ :=
  SpecialFunctions.reactiveArg (w.primary.L ^ 2 * (ρ₂ / |ω * w.M|) ^ 2)
    (w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψ₁ ^ 2)

/-- The optimizer `(u, v, r)` of the secondary-flux problem. -/
def arg₂ (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₂ : ℝ) : ℝ × ℝ × ℝ :=
  SpecialFunctions.reactiveArg (w.M ^ 2 * (ρ₂ / |ω * w.M|) ^ 2)
    (w.secondary.L ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψ₂ ^ 2)

variable {ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ}

/-- `P² = ω²/(4κ²) · (4 (p²a²)(q²b²) − (2(κ/ω)Q)²)` when `p q = κ |M|` and
`P² + Q² = (ωM)² a² b²`. -/
@[tmio T, powerlib_foundation] private theorem power_sq_scaled {P Q a b p q κ M ω : ℝ}
    (hω : ω ≠ 0) (hκ : κ ≠ 0) (hpq : (p * q) ^ 2 = (κ * M) ^ 2)
    (key : P ^ 2 + Q ^ 2 = (ω * M) ^ 2 * (a ^ 2 * b ^ 2)) :
    P ^ 2 = ω ^ 2 / (4 * κ ^ 2) *
      (4 * (p ^ 2 * a ^ 2) * (q ^ 2 * b ^ 2) - (2 * (κ / ω) * Q) ^ 2) := by
  have e : 4 * (p ^ 2 * a ^ 2) * (q ^ 2 * b ^ 2) = 4 * (p * q) ^ 2 * (a ^ 2 * b ^ 2) := by ring
  have e2 : ω ^ 2 / (4 * κ ^ 2) * (4 * (κ * M) ^ 2 * (a ^ 2 * b ^ 2) - (2 * (κ / ω) * Q) ^ 2) =
      (ω * M) ^ 2 * (a ^ 2 * b ^ 2) - Q ^ 2 := by
    field_simp
    ring
  rw [e, hpq, e2]
  linarith

/-- Under the bridges and `‖ψ₁‖² ≤ Ψ₁²`, whatever the reactive power: `P² ≤ limit₁`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_limit₁
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ limit₁ w ω ρ₁ ρ₂ Ψ₁ := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  obtain ⟨ha, hb⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hflux := Gyrator.normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  have key := Gyrator.power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  simp only [Complex.normSq_eq_norm_sq] at hflux key hψ
  have hu : w.primary.L ^ 2 * ‖I₁‖ ^ 2 ≤ w.primary.L ^ 2 * (ρ₂ / |ω * w.M|) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) (sq_nonneg _)
  have hv : w.M ^ 2 * ‖I₂‖ ^ 2 ≤ w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg _)
  have hS : w.primary.L ^ 2 * ‖I₁‖ ^ 2 + w.M ^ 2 * ‖I₂‖ ^ 2 +
      2 * (w.primary.L / ω) * (V₁ * conj I₁).im ≤ Ψ₁ ^ 2 := by linarith
  have hR := SpecialFunctions.le_reactiveMax (sq_nonneg Ψ₁) (by positivity) hu (by positivity) hv hS
  rw [power_sq_scaled (p := w.primary.L) (q := w.M) hω.ne' hL₁.ne' (by ring) key, limit₁]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

/-- Under the bridges and `‖ψ₂‖² ≤ Ψ₂²`, whatever the reactive power: `P² ≤ limit₂`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_limit₂
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ limit₂ w ω ρ₁ ρ₂ Ψ₂ := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  obtain ⟨ha, hb⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hflux := Gyrator.normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  have key := Gyrator.power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  have hQ : (V₂ * conj I₂).im = (V₁ * conj I₁).im := by
    rw [Gyrator.reactive₂_eq hX₁ hX₂ hR₁ hR₂ h, Gyrator.reactive₁_eq hX₁ hX₂ hR₁ hR₂ h]
  rw [hQ] at hflux
  simp only [Complex.normSq_eq_norm_sq] at hflux key hψ
  have hu : w.M ^ 2 * ‖I₁‖ ^ 2 ≤ w.M ^ 2 * (ρ₂ / |ω * w.M|) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) (sq_nonneg _)
  have hv : w.secondary.L ^ 2 * ‖I₂‖ ^ 2 ≤ w.secondary.L ^ 2 * (ρ₁ / |ω * w.M|) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg _)
  have hS : w.M ^ 2 * ‖I₁‖ ^ 2 + w.secondary.L ^ 2 * ‖I₂‖ ^ 2 +
      2 * (w.secondary.L / ω) * (V₁ * conj I₁).im ≤ Ψ₂ ^ 2 := by linarith
  have hR := SpecialFunctions.le_reactiveMax (sq_nonneg Ψ₂) (by positivity) hu (by positivity) hv hS
  rw [power_sq_scaled (p := w.M) (q := w.secondary.L) hω.ne' hL₂.ne' (by ring) key, limit₂]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

/-- The primary-flux optimizer is realized: admissible bridge phasors transfer `√limit₁`, with
`L₁²‖I₁‖² = u`, `M²‖I₂‖² = v` and `2(L₁/ω)Q = r` for `(u, v, r) = arg₁`. -/
@[tmio M, powerlib_domain] private theorem attain₁
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      (V₁ * conj I₁).re = Real.sqrt (limit₁ w ω ρ₁ ρ₂ Ψ₁) ∧
      w.primary.L ^ 2 * ‖I₁‖ ^ 2 = (arg₁ w ω ρ₁ ρ₂ Ψ₁).1 ∧
      w.M ^ 2 * ‖I₂‖ ^ 2 = (arg₁ w ω ρ₁ ρ₂ Ψ₁).2.1 ∧
      2 * (w.primary.L / ω) * (V₁ * conj I₁).im = (arg₁ w ω ρ₁ ρ₂ Ψ₁).2.2 := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hMa : 0 < |w.M| := abs_pos.mpr hM
  simp only [limit₁, arg₁]
  set A := ρ₂ / |ω * w.M| with hA
  set B := ρ₁ / |ω * w.M| with hB
  have hA0 : 0 ≤ A := div_nonneg hρ₂ hma.le
  have hB0 : 0 ≤ B := div_nonneg hρ₁ hma.le
  obtain ⟨hu0, huU, hv0, hvV, -⟩ := SpecialFunctions.reactiveArg_feasible
    (U := w.primary.L ^ 2 * A ^ 2) (V := w.M ^ 2 * B ^ 2) (by positivity) (by positivity)
    (sq_nonneg Ψ₁)
  have hval := SpecialFunctions.reactiveArg_value (w.primary.L ^ 2 * A ^ 2) (w.M ^ 2 * B ^ 2)
    (Ψ₁ ^ 2)
  have hnn := SpecialFunctions.reactiveMax_nonneg (U := w.primary.L ^ 2 * A ^ 2)
    (V := w.M ^ 2 * B ^ 2) (by positivity) (by positivity) (sq_nonneg Ψ₁)
  set u := (SpecialFunctions.reactiveArg (w.primary.L ^ 2 * A ^ 2) (w.M ^ 2 * B ^ 2) (Ψ₁ ^ 2)).1
  set v := (SpecialFunctions.reactiveArg (w.primary.L ^ 2 * A ^ 2) (w.M ^ 2 * B ^ 2) (Ψ₁ ^ 2)).2.1
  set r := (SpecialFunctions.reactiveArg (w.primary.L ^ 2 * A ^ 2) (w.M ^ 2 * B ^ 2) (Ψ₁ ^ 2)).2.2
  set R := SpecialFunctions.reactiveMax (w.primary.L ^ 2 * A ^ 2) (w.M ^ 2 * B ^ 2) (Ψ₁ ^ 2)
  have hlim : 0 ≤ ω ^ 2 / (4 * w.primary.L ^ 2) * R := by positivity
  have ha : Real.sqrt u / w.primary.L ≤ A := by
    rw [div_le_iff₀ hL₁]
    calc Real.sqrt u ≤ Real.sqrt ((w.primary.L * A) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact huU)
      _ = A * w.primary.L := by rw [Real.sqrt_sq (by positivity)]; ring
  have hb : Real.sqrt v / |w.M| ≤ B := by
    rw [div_le_iff₀ hMa]
    calc Real.sqrt v ≤ Real.sqrt ((|w.M| * B) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, sq_abs]; exact hvV)
      _ = B * |w.M| := by rw [Real.sqrt_sq (by positivity)]; ring
  have hua : w.primary.L ^ 2 * (Real.sqrt u / w.primary.L) ^ 2 = u := by
    rw [div_pow, Real.sq_sqrt hu0]; field_simp
  have hvb : w.M ^ 2 * (Real.sqrt v / |w.M|) ^ 2 = v := by
    rw [div_pow, Real.sq_sqrt hv0, sq_abs]; field_simp
  have hQ : 2 * (w.primary.L / ω) * (ω * r / (2 * w.primary.L)) = r := by field_simp
  have hPQ : Real.sqrt (ω ^ 2 / (4 * w.primary.L ^ 2) * R) ^ 2 + (ω * r / (2 * w.primary.L)) ^ 2 =
      (ω * w.M) ^ 2 * ((Real.sqrt u / w.primary.L) ^ 2 * (Real.sqrt v / |w.M|) ^ 2) := by
    rw [Real.sq_sqrt hlim, ← hval]
    simp only [div_pow, Real.sq_sqrt hu0, Real.sq_sqrt hv0, sq_abs]
    field_simp
    ring
  obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hP, hQ'⟩ :=
    Gyrator.exists_realization hX₁ hX₂ hR₁ hR₂ hm (by positivity) (by positivity) ha hb hPQ
  refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP, ?_, ?_, ?_⟩
  · rw [hI₁, hua]
  · rw [hI₂, hvb]
  · rw [hQ', hQ]

/-- The exact largest power under the bridges and the primary flux bound, whatever the reactive
power: `√limit₁`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power₁
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt (limit₁ w ω ρ₁ ρ₂ Ψ₁)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP, hu, hv, hr⟩ :=
      attain₁ (Ψ₁ := Ψ₁) hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, hP.symm⟩
    have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
    have hma : 0 < |ω * w.M| := abs_pos.mpr hm
    obtain ⟨-, -, -, -, hS⟩ := SpecialFunctions.reactiveArg_feasible
      (U := w.primary.L ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (V := w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2)
      (by positivity) (by positivity) (sq_nonneg Ψ₁)
    rw [Gyrator.normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hu, hv, hr]
    exact hS
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_limit₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM h h₁ h₂ hψ))

/-- The secondary-flux optimizer is realized: admissible bridge phasors transfer `√limit₂`, with
`M²‖I₁‖² = u`, `L₂²‖I₂‖² = v` and `2(L₂/ω)Q = r` for `(u, v, r) = arg₂`. -/
@[tmio M, powerlib_domain] private theorem attain₂
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      (V₁ * conj I₁).re = Real.sqrt (limit₂ w ω ρ₁ ρ₂ Ψ₂) ∧
      w.M ^ 2 * ‖I₁‖ ^ 2 = (arg₂ w ω ρ₁ ρ₂ Ψ₂).1 ∧
      w.secondary.L ^ 2 * ‖I₂‖ ^ 2 = (arg₂ w ω ρ₁ ρ₂ Ψ₂).2.1 ∧
      2 * (w.secondary.L / ω) * (V₁ * conj I₁).im = (arg₂ w ω ρ₁ ρ₂ Ψ₂).2.2 := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hMa : 0 < |w.M| := abs_pos.mpr hM
  simp only [limit₂, arg₂]
  set A := ρ₂ / |ω * w.M| with hA
  set B := ρ₁ / |ω * w.M| with hB
  have hA0 : 0 ≤ A := div_nonneg hρ₂ hma.le
  have hB0 : 0 ≤ B := div_nonneg hρ₁ hma.le
  obtain ⟨hu0, huU, hv0, hvV, -⟩ := SpecialFunctions.reactiveArg_feasible
    (U := w.M ^ 2 * A ^ 2) (V := w.secondary.L ^ 2 * B ^ 2) (by positivity) (by positivity)
    (sq_nonneg Ψ₂)
  have hval := SpecialFunctions.reactiveArg_value (w.M ^ 2 * A ^ 2) (w.secondary.L ^ 2 * B ^ 2)
    (Ψ₂ ^ 2)
  have hnn := SpecialFunctions.reactiveMax_nonneg (U := w.M ^ 2 * A ^ 2)
    (V := w.secondary.L ^ 2 * B ^ 2) (by positivity) (by positivity) (sq_nonneg Ψ₂)
  set u := (SpecialFunctions.reactiveArg (w.M ^ 2 * A ^ 2) (w.secondary.L ^ 2 * B ^ 2) (Ψ₂ ^ 2)).1
  set v := (SpecialFunctions.reactiveArg (w.M ^ 2 * A ^ 2) (w.secondary.L ^ 2 * B ^ 2)
    (Ψ₂ ^ 2)).2.1
  set r := (SpecialFunctions.reactiveArg (w.M ^ 2 * A ^ 2) (w.secondary.L ^ 2 * B ^ 2)
    (Ψ₂ ^ 2)).2.2
  set R := SpecialFunctions.reactiveMax (w.M ^ 2 * A ^ 2) (w.secondary.L ^ 2 * B ^ 2) (Ψ₂ ^ 2)
  have hlim : 0 ≤ ω ^ 2 / (4 * w.secondary.L ^ 2) * R := by positivity
  have ha : Real.sqrt u / |w.M| ≤ A := by
    rw [div_le_iff₀ hMa]
    calc Real.sqrt u ≤ Real.sqrt ((|w.M| * A) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, sq_abs]; exact huU)
      _ = A * |w.M| := by rw [Real.sqrt_sq (by positivity)]; ring
  have hb : Real.sqrt v / w.secondary.L ≤ B := by
    rw [div_le_iff₀ hL₂]
    calc Real.sqrt v ≤ Real.sqrt ((w.secondary.L * B) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact hvV)
      _ = B * w.secondary.L := by rw [Real.sqrt_sq (by positivity)]; ring
  have hua : w.M ^ 2 * (Real.sqrt u / |w.M|) ^ 2 = u := by
    rw [div_pow, Real.sq_sqrt hu0, sq_abs]; field_simp
  have hvb : w.secondary.L ^ 2 * (Real.sqrt v / w.secondary.L) ^ 2 = v := by
    rw [div_pow, Real.sq_sqrt hv0]; field_simp
  have hQ : 2 * (w.secondary.L / ω) * (ω * r / (2 * w.secondary.L)) = r := by field_simp
  have hPQ : Real.sqrt (ω ^ 2 / (4 * w.secondary.L ^ 2) * R) ^ 2 +
      (ω * r / (2 * w.secondary.L)) ^ 2 =
      (ω * w.M) ^ 2 * ((Real.sqrt u / |w.M|) ^ 2 * (Real.sqrt v / w.secondary.L) ^ 2) := by
    rw [Real.sq_sqrt hlim, ← hval]
    simp only [div_pow, Real.sq_sqrt hu0, Real.sq_sqrt hv0, sq_abs]
    field_simp
    ring
  obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hP, hQ'⟩ :=
    Gyrator.exists_realization hX₁ hX₂ hR₁ hR₂ hm (by positivity) (by positivity) ha hb hPQ
  refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP, ?_, ?_, ?_⟩
  · rw [hI₁, hua]
  · rw [hI₂, hvb]
  · rw [hQ', hQ]

/-- The exact largest power under the bridges and the secondary flux bound, whatever the
reactive power: `√limit₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power₂
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt (limit₂ w ω ρ₁ ρ₂ Ψ₂)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP, hu, hv, hr⟩ :=
      attain₂ (Ψ₂ := Ψ₂) hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hρ₁ hρ₂
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, hP.symm⟩
    have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
    have hma : 0 < |ω * w.M| := abs_pos.mpr hm
    obtain ⟨-, -, -, -, hS⟩ := SpecialFunctions.reactiveArg_feasible
      (U := w.M ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (V := w.secondary.L ^ 2 * (ρ₁ / |ω * w.M|) ^ 2)
      (by positivity) (by positivity) (sq_nonneg Ψ₂)
    have hQ : (V₂ * conj I₂).im = (V₁ * conj I₁).im := by
      rw [Gyrator.reactive₂_eq hX₁ hX₂ hR₁ hR₂ h, Gyrator.reactive₁_eq hX₁ hX₂ hR₁ hR₂ h]
    rw [Gyrator.normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, hQ, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hu, hv, hr]
    exact hS
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_limit₂ hX₁ hX₂ hR₁ hR₂ hω hL₂ hM h h₁ h₂ hψ))

/-! ## Both flux bounds -/

/-- Under the bridges and both flux bounds, whatever the reactive power: `P² ≤ min(limit₁,
limit₂)`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_both
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hL₂ : 0 < w.secondary.L) (hM : w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁)
    (h₂ : ‖V₂‖ ≤ ρ₂) (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ min (limit₁ w ω ρ₁ ρ₂ Ψ₁) (limit₂ w ω ρ₁ ρ₂ Ψ₂) :=
  le_min (power_sq_le_limit₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM h h₁ h₂ hψ₁)
    (power_sq_le_limit₂ hX₁ hX₂ hR₁ hR₂ hω hL₂ hM h h₁ h₂ hψ₂)

/-- Both flux bounds, the primary one binding: if the primary-flux optimizer `(u, v, r) = arg₁`
meets the secondary bound, `(M²/L₁²) u + (L₂²/M²) v + (L₂/L₁) r ≤ Ψ₂²`, the exact largest power
under both bounds is `√limit₁`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_both₁
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hslack : w.M ^ 2 / w.primary.L ^ 2 * (arg₁ w ω ρ₁ ρ₂ Ψ₁).1 +
      w.secondary.L ^ 2 / w.M ^ 2 * (arg₁ w ω ρ₁ ρ₂ Ψ₁).2.1 +
      w.secondary.L / w.primary.L * (arg₁ w ω ρ₁ ρ₂ Ψ₁).2.2 ≤ Ψ₂ ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re} (Real.sqrt (limit₁ w ω ρ₁ ρ₂ Ψ₁)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP, hu, hv, hr⟩ :=
      attain₁ (Ψ₁ := Ψ₁) hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂
    obtain ⟨-, hψ, -⟩ := (isGreatest_power₁ (Ψ₁ := Ψ₁) hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂).1
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, ?_, hP.symm⟩
    · have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
      have hma : 0 < |ω * w.M| := abs_pos.mpr hm
      obtain ⟨-, -, -, -, hS⟩ := SpecialFunctions.reactiveArg_feasible
        (U := w.primary.L ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (V := w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2)
        (by positivity) (by positivity) (sq_nonneg Ψ₁)
      rw [Gyrator.normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, hu, hv, hr]
      exact hS
    · have hQ : (V₂ * conj I₂).im = (V₁ * conj I₁).im := by
        rw [Gyrator.reactive₂_eq hX₁ hX₂ hR₁ hR₂ h, Gyrator.reactive₁_eq hX₁ hX₂ hR₁ hR₂ h]
      rw [Gyrator.normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, hQ, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq]
      have e : w.M ^ 2 * ‖I₁‖ ^ 2 + w.secondary.L ^ 2 * ‖I₂‖ ^ 2 +
          2 * (w.secondary.L / ω) * (V₁ * conj I₁).im =
          w.M ^ 2 / w.primary.L ^ 2 * (w.primary.L ^ 2 * ‖I₁‖ ^ 2) +
            w.secondary.L ^ 2 / w.M ^ 2 * (w.M ^ 2 * ‖I₂‖ ^ 2) +
            w.secondary.L / w.primary.L * (2 * (w.primary.L / ω) * (V₁ * conj I₁).im) := by
        field_simp
      rw [e]
      rw [← hu, ← hv, ← hr] at hslack
      exact hslack
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, -, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_limit₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM h h₁ h₂ hψ))

/-- Both flux bounds, the secondary one binding: if the secondary-flux optimizer
`(u, v, r) = arg₂` meets the primary bound, `(L₁²/M²) u + (M²/L₂²) v + (L₁/L₂) r ≤ Ψ₁²`, the exact
largest power under both bounds is `√limit₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_both₂
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hslack : w.primary.L ^ 2 / w.M ^ 2 * (arg₂ w ω ρ₁ ρ₂ Ψ₂).1 +
      w.M ^ 2 / w.secondary.L ^ 2 * (arg₂ w ω ρ₁ ρ₂ Ψ₂).2.1 +
      w.primary.L / w.secondary.L * (arg₂ w ω ρ₁ ρ₂ Ψ₂).2.2 ≤ Ψ₁ ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re} (Real.sqrt (limit₂ w ω ρ₁ ρ₂ Ψ₂)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP, hu, hv, hr⟩ :=
      attain₂ (Ψ₂ := Ψ₂) hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hρ₁ hρ₂
    obtain ⟨-, hψ, -⟩ := (isGreatest_power₂ (Ψ₂ := Ψ₂) hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hρ₁ hρ₂).1
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, ?_, hP.symm⟩
    · rw [Gyrator.normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq]
      have e : w.primary.L ^ 2 * ‖I₁‖ ^ 2 + w.M ^ 2 * ‖I₂‖ ^ 2 +
          2 * (w.primary.L / ω) * (V₁ * conj I₁).im =
          w.primary.L ^ 2 / w.M ^ 2 * (w.M ^ 2 * ‖I₁‖ ^ 2) +
            w.M ^ 2 / w.secondary.L ^ 2 * (w.secondary.L ^ 2 * ‖I₂‖ ^ 2) +
            w.primary.L / w.secondary.L * (2 * (w.secondary.L / ω) * (V₁ * conj I₁).im) := by
        field_simp
      rw [e, hu, hv, hr]
      exact hslack
    · have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
      have hma : 0 < |ω * w.M| := abs_pos.mpr hm
      obtain ⟨-, -, -, -, hS⟩ := SpecialFunctions.reactiveArg_feasible
        (U := w.M ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (V := w.secondary.L ^ 2 * (ρ₁ / |ω * w.M|) ^ 2)
        (by positivity) (by positivity) (sq_nonneg Ψ₂)
      have hQ : (V₂ * conj I₂).im = (V₁ * conj I₁).im := by
        rw [Gyrator.reactive₂_eq hX₁ hX₂ hR₁ hR₂ h, Gyrator.reactive₁_eq hX₁ hX₂ hR₁ hR₂ h]
      rw [Gyrator.normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, hQ, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, hu, hv, hr]
      exact hS
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, -, hψ, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_limit₂ hX₁ hX₂ hR₁ hR₂ hω hL₂ hM h h₁ h₂ hψ))

end powerlib.WPT.ReactiveLimits
