import theorem.GFM.VSMLPF

/-! # Reduced-layer algebra of the GFM VSM + power-filter model

Foundation identities for the three-state model of `theorem/GFM/VSMLPF.lean` (state
`(δ, ω, P_f)`, `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin(δ − u) − P_f)`,
`K₀ = E V_g / X_g`, export-positive active power, continuous time).  None of them is a
stability statement; the domain results live in `VSMLPF.lean`.

* `hasDerivAt_powerAngle`, `K_eq_deriv`: `K = ∂P/∂δ = E V_g cos δ₀ / X_g`;
  `exists_equilibrium_iff_EVX`: equilibria exist iff `|P₀| ≤ E V_g / X_g`.
* `texact_denominator_expansion`: the exact identity
  `[(s + ω_c)(M s² + D s) + ω_c K] / (M (s + ω_c)) = s² + 2α_red s + K/M + R(s)`,
  `2α_red = D/M − K/(M ω_c)`, `R(s) = K s² / (M ω_c (s + ω_c))` (the first-order filter
  expansion behind the reduced swing layer).
* `reduced_root_re`: a non-real root of `s² + 2α s + ω₀²` has real part `−α`.
* `twoAlphaRed_pos_iff`: `2α_red > 0 ⇔ r_c < 2ζ_sw` (`r_c = ω₀/ω_c`, `ζ_sw = D/(2√(MK))`);
  `twoAlphaRed_eq_zero_iff`: the zero of `α_red` is `ω_c = K/D`, which differs from the exact
  Routh–Hurwitz boundary `ω_c = K/D − D/M` by `D/M`.
* `iteratedDeriv_jacobian_u`: `f_xuu = ∂²J/∂u² |_{u=0} = −(A₀)_{P_f δ} e_{P_f} e_δᵀ`.
* `boundary_eigenpairs`: on the Routh boundary both `±j ω_H` are eigenvalues of `A₀`.

Family and connection conclusions: none.  The stability conclusions of the model are the
connection statements of `VSMLPF.family` (`theorem/GFM/VSMLPF.lean`); the former domain theorem
`exists_equilibrium_iff_EVX` is static evidence on the model.

Source: work-sync projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §15 ("摆动二阶约化", "混合张量"); notes/theory-draft.md §2.4.
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix

/-- `d/dδ [(E V_g / X_g) sin δ] = E V_g cos δ / X_g`. -/
@[powerlib_foundation] theorem hasDerivAt_powerAngle (E Vg Xg δ : ℝ) :
    HasDerivAt (fun x => E * Vg / Xg * Real.sin x) (E * Vg * Real.cos δ / Xg) δ := by
  convert (Real.hasDerivAt_sin δ).const_mul (E * Vg / Xg) using 1
  ring

namespace VSMLPF

variable (g : VSMLPF)

/-- The synchronizing coefficient is the slope of the power-angle curve at `δ₀`:
`K = K₀ cos δ₀ = ∂(K₀ sin δ)/∂δ |_{δ₀}`. -/
@[powerlib_foundation] theorem K_eq_deriv :
    HasDerivAt (fun x => g.K0 * Real.sin x) g.K g.δ0 :=
  (Real.hasDerivAt_sin g.δ0).const_mul g.K0

/-- With `K₀ = E V_g / X_g`, equilibria exist iff `|P₀| ≤ E V_g / X_g`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem exists_equilibrium_iff_EVX {E Vg Xg : ℝ} (hK0 : g.K0 = E * Vg / Xg)
    (hM : g.M ≠ 0) (hω : g.ωc ≠ 0) (hpos : 0 < E * Vg / Xg) :
    (∃ x, g.field x = 0) ↔ |g.P0| ≤ E * Vg / Xg := by
  rw [← hK0]
  exact g.exists_equilibrium_iff hM hω (hK0 ▸ hpos)

/-- Reduced-layer damping `2α_red = D/M − K/(M ω_c)`. -/
def twoAlphaRed : ℝ := g.D / g.M - g.K / (g.M * g.ωc)

/-- Exact first-order filter expansion of the `u → δ` denominator:
`[(s + ω_c)(M s² + D s) + ω_c K] / (M (s + ω_c)) = s² + 2α_red s + K/M + K s²/(M ω_c (s + ω_c))`. -/
@[powerlib_foundation] theorem texact_denominator_expansion (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    {s : ℂ} (hs : s + (g.ωc : ℂ) ≠ 0) :
    ((s + (g.ωc : ℂ)) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) + (g.ωc : ℂ) * (g.K : ℂ)) /
        ((g.M : ℂ) * (s + (g.ωc : ℂ))) =
      s ^ 2 + (g.twoAlphaRed : ℂ) * s + (g.K : ℂ) / (g.M : ℂ) +
        (g.K : ℂ) * s ^ 2 / ((g.M : ℂ) * (g.ωc : ℂ) * (s + (g.ωc : ℂ))) := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hω' : (g.ωc : ℂ) ≠ 0 := by exact_mod_cast hω
  simp only [twoAlphaRed]
  push_cast
  field_simp
  ring

variable {g}

/-- `2α_red > 0 ⇔ r_c < 2 ζ_sw` with `r_c = √(K/M)/ω_c`, `ζ_sw = D/(2√(MK))`
(`M, K, ω_c > 0`). -/
@[powerlib_foundation] theorem twoAlphaRed_pos_iff (hM : 0 < g.M) (hK : 0 < g.K) (hω : 0 < g.ωc) :
    0 < g.twoAlphaRed ↔
      Real.sqrt (g.K / g.M) / g.ωc < 2 * (g.D / (2 * Real.sqrt (g.M * g.K))) := by
  have hs : 0 < Real.sqrt (g.M * g.K) := Real.sqrt_pos.mpr (mul_pos hM hK)
  have hprod : Real.sqrt (g.K / g.M) * Real.sqrt (g.M * g.K) = g.K := by
    rw [← Real.sqrt_mul (div_nonneg hK.le hM.le), show g.K / g.M * (g.M * g.K) = g.K ^ 2 by
      field_simp, Real.sqrt_sq hK.le]
  have e1 : 0 < g.twoAlphaRed ↔ g.K < g.D * g.ωc := by
    rw [twoAlphaRed, sub_pos, div_lt_div_iff₀ (mul_pos hM hω) hM]
    constructor <;> intro h <;> nlinarith
  have e2 : Real.sqrt (g.K / g.M) / g.ωc < 2 * (g.D / (2 * Real.sqrt (g.M * g.K))) ↔
      g.K < g.D * g.ωc := by
    rw [show 2 * (g.D / (2 * Real.sqrt (g.M * g.K))) = g.D / Real.sqrt (g.M * g.K) by
      field_simp, div_lt_div_iff₀ hω hs, hprod]
  rw [e1, e2]

/-- The zero of `α_red` is `ω_c = K/D`; it differs from the exact Routh–Hurwitz (Hopf) boundary
`ω_c* = K/D − D/M` by `D/M`. -/
@[powerlib_foundation] theorem twoAlphaRed_eq_zero_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) :
    g.twoAlphaRed = 0 ↔ g.ωc = g.K / g.D := by
  rw [twoAlphaRed, sub_eq_zero, div_eq_div_iff hM.ne' (mul_pos hM hω).ne',
    eq_div_iff hD.ne']
  constructor <;> intro h <;> nlinarith

/-- A non-real root of the reduced quadratic `s² + 2α s + ω₀²` has real part `−α`
(so `α_red` is the decay rate of the reduced swing pair). -/
@[powerlib_foundation] theorem reduced_root_re {α ω0sq : ℝ} {s : ℂ}
    (hs : s ^ 2 + 2 * (α : ℂ) * s + (ω0sq : ℂ) = 0) (him : s.im ≠ 0) : s.re = -α := by
  have h := congrArg Complex.im hs
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, pow_two,
    Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re] at h
  have : (2 * s.re + 2 * α) * s.im = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 him

variable (g)

/-- `∂J/∂u` along `u ↦ J(δ₀ − u)` at a general `u`: only the `(P_f, δ)` entry varies. -/
def jacobianU' (u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, 0, 0; g.ωc * (g.K0 * Real.sin (g.δ0 - u)), 0, 0]

/-- `f_xuu = −(A₀)_{P_f δ} e_{P_f} e_δᵀ`, `A₀ = J(δ₀)`. -/
def fxuu : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; -(g.jacobian g.δ0 2 0), 0, 0]

@[powerlib_foundation] theorem hasDerivAt_jacobian_entry (u : ℝ) (i j : Fin 3) :
    HasDerivAt (fun v => g.jacobian (g.δ0 - v) i j) (g.jacobianU' u i j) u := by
  have h1 : HasDerivAt (fun v : ℝ => g.δ0 - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub g.δ0
  have key : HasDerivAt (fun v => g.ωc * (g.K0 * Real.cos (g.δ0 - v)))
      (g.ωc * (g.K0 * Real.sin (g.δ0 - u))) u := by
    convert ((h1.cos).const_mul g.K0).const_mul g.ωc using 1
    ring
  fin_cases i <;> fin_cases j <;> simp [jacobian, jacobianU'] <;>
    first | exact hasDerivAt_const _ _ | exact key

/-- **Mixed tensor `f_xuu`**: `∂²/∂u² J(δ₀ − u) |_{u=0} = −(A₀)_{P_f δ} e_{P_f} e_δᵀ`
(entrywise). -/
@[powerlib_foundation] theorem iteratedDeriv_jacobian_u (i j : Fin 3) :
    iteratedDeriv 2 (fun u => g.jacobian (g.δ0 - u) i j) 0 = g.fxuu i j := by
  have hd : deriv (fun u => g.jacobian (g.δ0 - u) i j) = fun u => g.jacobianU' u i j :=
    funext fun u => (g.hasDerivAt_jacobian_entry u i j).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  have h1 : HasDerivAt (fun v : ℝ => g.δ0 - v) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub g.δ0
  have key : HasDerivAt (fun v => g.ωc * (g.K0 * Real.sin (g.δ0 - v)))
      (-(g.ωc * (g.K0 * Real.cos g.δ0))) 0 := by
    convert ((h1.sin).const_mul g.K0).const_mul g.ωc using 1
    simp
  have h2 : HasDerivAt (fun u => g.jacobianU' u i j) (g.fxuu i j) 0 := by
    fin_cases i <;> fin_cases j <;> simp [jacobianU', fxuu, jacobian] <;>
      first | exact hasDerivAt_const _ _ | exact key
  exact h2.deriv

/-- On the Routh–Hurwitz boundary `ω_c = K/D − D/M` both `±j ω_H`, `ω_H² = K/M − D²/M²`, are
eigenvalues of the Jacobian at the loading equilibrium. -/
@[powerlib_foundation] theorem boundary_eigenpairs (hM : g.M ≠ 0) (hD : g.D ≠ 0)
    (hωc : g.ωc = g.K / g.D - g.D / g.M) {ωH : ℝ}
    (hH : ωH ^ 2 = g.K / g.M - g.D ^ 2 / g.M ^ 2) :
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧
        (g.jacobian g.δ0).map (algebraMap ℝ ℂ) *ᵥ v = ((ωH : ℂ) * Complex.I) • v) ∧
      ∃ v : Fin 3 → ℂ, v ≠ 0 ∧
        (g.jacobian g.δ0).map (algebraMap ℝ ℂ) *ᵥ v = (((-ωH : ℝ) : ℂ) * Complex.I) • v := by
  refine ⟨Criteria.exists_eigenpair_of_det_characteristicMatrix_eq_zero _
      (g.det_characteristicMatrix_boundary hM hD hωc hH),
    Criteria.exists_eigenpair_of_det_characteristicMatrix_eq_zero _
      (g.det_characteristicMatrix_boundary hM hD hωc (by rw [neg_sq]; exact hH))⟩

end VSMLPF
end powerlib.GFM
