import theorem.NormalForm.Hopf

/-! # Radial linearization rate at the Hopf cycle

The radial amplitude equation `ṙ = μ r + l₁ r³` of the truncated Hopf normal form has the cycle
radius `R = √(−μ/l₁)` as an equilibrium with linearization rate `−2μ`. For the normal form of a
limit cycle used by the periodogram method this identifies the parameters of the limit-cycle
row of Table 3-1: amplitude `λ = √γ`, frequency `α = ω_h`, and amplitude-relaxation rate
`2γ = 2λ²` (the rate of the amplitude fluctuation `p` in (3-28) and (3-36)).

Scope.
* The truncated Hopf normal form `Hopf.Params` / `Hopf.field` of
  `theorem/NormalForm/Hopf.lean`: deterministic, continuous time, no noise, no `O(|z|⁴)`
  remainder. Its polar form (`Hopf.radius_hasDerivWithinAt`: `ṙ = μr + l₁r³` along solutions;
  `Hopf.angular_identity`: `θ̇ = ω₀ + κr²`), the invariant circle, its frequency and its
  attraction (`Hopf.supercritical_isAttractingLimitCycle`) are used from there, not restated.
* The noise terms of (3-26)–(3-28) and the report's claim that the amplitude fluctuation is an
  Ornstein–Uhlenbeck process are outside the scope: only the deterministic linearization rate
  that (3-28) assigns to that process is proved here. A normal form, not an engineering model.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1,
eqs. (3-26)–(3-28) and Table 3-1 (limit-cycle row).

Results.
* `radialField` — `r ↦ μr + l₁r³`, the radial field of `Hopf.radius_hasDerivWithinAt`.
* `radialField_radius`, `hasDerivAt_radialField_radius` — for `l₁ ≠ 0` and `−μ/l₁ ≥ 0` the cycle
  radius `R = √(−μ/l₁)` is an equilibrium of the radial field and its linearization rate there
  is `−2μ` (exactly, not to leading order).
* `tr110Params`, `tr110_limitCycle` — for (3-26) without noise, `ż = (γ + iω_h) z − |z|² z`
  (`μ = γ`, `ω₀ = ω_h`, `l₁ = −1`, `κ = 0`) and `γ > 0`: radius `√γ`, cycle frequency `ω_h`, and
  radial rate `−2γ = −2(√γ)²`, i.e. `λ = √γ`, `α = ω_h` and the OU rate `2λ²` of (3-36). With
  `ω_h ≠ 0` the cycle is an attracting limit cycle by `Hopf.supercritical_isAttractingLimitCycle`
  (`μ = γ > 0`, `l₁ = −1 < 0`).
-/

noncomputable section
namespace powerlib.NormalForm.Hopf

/-- The radial field `r ↦ μ r + l₁ r³` of the truncated Hopf normal form. -/
def radialField (p : Params) (r : ℝ) : ℝ := p.μ * r + p.l₁ * r ^ 3

/-- The cycle radius is an equilibrium of the radial field. -/
@[tmio M, powerlib_foundation] theorem radialField_radius (p : Params) (hl : p.l₁ ≠ 0)
    (hR : 0 ≤ -p.μ / p.l₁) : radialField p (radius p) = 0 := by
  have h2 := radius_sq p hR
  unfold radialField
  rw [show radius p ^ 3 = radius p * radius p ^ 2 by ring, h2]
  field_simp
  ring

/-- **Radial linearization rate at the cycle**: `d/dr (μr + l₁r³)` at `R = √(−μ/l₁)` is `−2μ`. -/
@[tmio M, powerlib_foundation] theorem hasDerivAt_radialField_radius (p : Params) (hl : p.l₁ ≠ 0)
    (hR : 0 ≤ -p.μ / p.l₁) : HasDerivAt (radialField p) (-2 * p.μ) (radius p) := by
  have h := ((hasDerivAt_id (radius p)).const_mul p.μ).add
    ((hasDerivAt_pow 3 (radius p)).const_mul p.l₁)
  have hf : radialField p = (fun y => p.μ * id y) + fun y => p.l₁ * y ^ 3 := by
    funext r; simp [radialField]
  rw [hf]
  convert h using 1
  have h2 := radius_sq p hR
  rw [show (3 : ℕ) - 1 = 2 by norm_num, h2]
  push_cast
  field_simp
  ring

/-- Parameters of TR-110 (3-26) without noise: `μ = γ`, `ω₀ = ω_h`, `l₁ = −1`, `κ = 0`. -/
def tr110Params (γ ωh : ℝ) : Params := ⟨γ, ωh, -1, 0⟩

/-- **Table 3-1, limit-cycle row.** For `ż = (γ + iω_h) z − |z|² z`, `γ > 0`: the cycle radius is
`√γ` (`λ`), the cycle frequency is `ω_h` (`α`), and the radial linearization rate at the cycle
is `−2γ = −2(√γ)²` (the OU rate `2λ²` of the amplitude fluctuation). -/
@[tmio M, powerlib_foundation] theorem tr110_limitCycle {γ : ℝ} (hγ : 0 < γ) (ωh : ℝ) :
    radius (tr110Params γ ωh) = √γ ∧ frequency (tr110Params γ ωh) = ωh ∧
      HasDerivAt (radialField (tr110Params γ ωh)) (-2 * √γ ^ 2) (radius (tr110Params γ ωh)) := by
  have hrad : radius (tr110Params γ ωh) = √γ := by
    simp [radius, tr110Params]
  refine ⟨hrad, by simp [frequency, tr110Params], ?_⟩
  have h := hasDerivAt_radialField_radius (tr110Params γ ωh) (by simp [tr110Params])
    (by simp [tr110Params]; exact hγ.le)
  rwa [Real.sq_sqrt hγ.le]

end powerlib.NormalForm.Hopf
