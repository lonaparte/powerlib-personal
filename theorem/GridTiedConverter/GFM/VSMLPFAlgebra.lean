import theorem.GridTiedConverter.GFM.VSMLPF

/-! # Reduced-layer algebra of the GFM VSM + power-filter model

Algebraic model identities for the three-state VSM + power-filter model.  None of them is a stability
statement; the domain results live in `VSMLPF.lean`.

Model boundary.
The three-state model of `theorem/GridTiedConverter/GFM/VSMLPF.lean` (state `(δ, ω, P_f)`, `δ̇ = ω`,
`M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin(δ − u) − P_f)`, `K₀ = E V_g / X_g`, export-positive
active power, continuous time), with the grid-angle or `P_ref` modulation `u` as input.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md` §15 ("摆动二阶约化", "混合张量"); `notes/theory-draft.md` §2.4,
§1.3 (GFM model); GFM channels: `projects/gfl-gfm-stability-tree/notes/concepts/
nonautonomous-criteria.md` (GFM `P_ref` 通道 `A_u = 0`).

Results.
* The synchronizing coefficient `K = ∂P/∂δ = K₀ cos δ₀` (`= E V_g cos δ₀ / X_g`) is the slope of
  the power-angle curve at the loading angle: `Synchronous.SwingParams.hasDerivAt_Pe` of the
  second-order swing reduction `swingReduced M D P₀ K₀` (`GFM.swingReduced`) at `δ₀`; with
  `K₀ = E V_g / X_g` equilibria exist iff `|P₀| ≤ E V_g / X_g` (`VSMLPF.exists_equilibrium_iff`).
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
* GFM channels (no separate model): a `P_ref` deviation `u` is the parameter map `P₀ ↦ P₀ + u` of
  `VSMLPF`, which leaves the Jacobian `VSMLPF.jacobian δ` unchanged (it does not contain `P₀`), so
  `A_u = ∂_u ∂_z f = 0`; a grid-angle deviation `u` is `VSMLPF.fieldU u`, with Jacobian `J(δ − u)`
  (`VSMLPF.fderiv_fieldU`), whose `u`-derivative at `0` is `A₁ = ω_c P₀ e_{P_f} e_δᵀ`
  (`VSMLPF.hasDerivAt_jacobian_u`, entrywise `hasDerivAt_jacobian_entry`), nonzero exactly at a
  loaded operating point `P₀ ≠ 0` (`VSMLPF.A1_ne_zero_iff`).
Family and connection conclusions.
None.  The stability conclusions of the model are the connection statements of `VSMLPF.family`
(`theorem/GridTiedConverter/GFM/VSMLPF.lean`).
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix

namespace VSMLPF

variable (g : VSMLPF)

/-- Reduced-layer damping `2α_red = D/M − K/(M ω_c)`. -/
def twoAlphaRed : ℝ := g.D / g.M - g.K / (g.M * g.ωc)

/-- Exact first-order filter expansion of the `u → δ` denominator:
`[(s + ω_c)(M s² + D s) + ω_c K] / (M (s + ω_c)) = s² + 2α_red s + K/M + K s²/(M ω_c (s + ω_c))`. -/
@[tmio M, powerlib_domain] theorem texact_denominator_expansion (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
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
@[tmio M, powerlib_domain] theorem twoAlphaRed_pos_iff (hM : 0 < g.M) (hK : 0 < g.K) (hω : 0 < g.ωc) :
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
@[tmio M, powerlib_domain] theorem twoAlphaRed_eq_zero_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) :
    g.twoAlphaRed = 0 ↔ g.ωc = g.K / g.D := by
  rw [twoAlphaRed, sub_eq_zero, div_eq_div_iff hM.ne' (mul_pos hM hω).ne',
    eq_div_iff hD.ne']
  constructor <;> intro h <;> nlinarith

/-- A non-real root of the reduced quadratic `s² + 2α s + ω₀²` has real part `−α`
(so `α_red` is the decay rate of the reduced swing pair). -/
@[tmio T, powerlib_foundation] theorem reduced_root_re {α ω0sq : ℝ} {s : ℂ}
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

@[tmio M, powerlib_domain] theorem hasDerivAt_jacobian_entry (u : ℝ) (i j : Fin 3) :
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
@[tmio M, powerlib_domain] theorem iteratedDeriv_jacobian_u (i j : Fin 3) :
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
@[tmio M, powerlib_domain] theorem boundary_eigenpairs (hM : g.M ≠ 0) (hD : g.D ≠ 0)
    (hωc : g.ωc = g.K / g.D - g.D / g.M) {ωH : ℝ}
    (hH : ωH ^ 2 = g.K / g.M - g.D ^ 2 / g.M ^ 2) :
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧
        (g.jacobian g.δ0).map (algebraMap ℝ ℂ) *ᵥ v = ((ωH : ℂ) * Complex.I) • v) ∧
      ∃ v : Fin 3 → ℂ, v ≠ 0 ∧
        (g.jacobian g.δ0).map (algebraMap ℝ ℂ) *ᵥ v = (((-ωH : ℝ) : ℂ) * Complex.I) • v := by
  refine ⟨Linear.exists_eigenvector_of_root
      (g.det_characteristicMatrix_boundary hM hD hωc hH),
    Linear.exists_eigenvector_of_root
      (g.det_characteristicMatrix_boundary hM hD hωc (by rw [neg_sq]; exact hH))⟩

end VSMLPF

end powerlib.GFM
