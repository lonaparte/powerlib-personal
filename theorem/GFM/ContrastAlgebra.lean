import theorem.Dynamics.Locality

/-! # Algebra of the GFL/GFM tuning-knob comparison (§17)

Foundation layer: polynomial and calculus identities used by the GFL/GFM parametric-contrast
note.  None of these is an engineering conclusion by itself.

Model boundary.
The three-state VSM + low-pass field `(δ, ω, P_f)` of the contrast note's `GFM` model
(`gfmField`: `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (E(δ) V sin δ / X − P_f)`, emf
law `E(δ)` with PCC or internal-emf Q-sensing), its characteristic polynomial
`(s + ω_c)(M s² + D s) + ω_c K` and the transfer `T_exact`; polynomial identities over `ℂ`.

Convention: active power export-positive (GFM family exception, work-sync conventions §D9).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md` §17; `.../gfl-gfm-contrast/archive/notes/concepts/
contrast-conclusions.md` 推论三 (`K_q = 0` 严格零), model `GFM` in
`.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`.

Results.
* `beta3_family`: for `α₀ > 0`, `ν > 0` and `β₃ > 2(α₀ + ν)` there are positive `D, K, ω_c`
  (any `M > 0`) with `(s + ω_c)(M s² + D s) + ω_c K = M (s + β₃)(s² + 2α₀ s + ν²)` for every
  complex `s`: the three-state VSM + low-pass characteristic polynomial (`/M`) has spectrum
  exactly `{−β₃} ∪ {roots of s² + 2α₀ s + ν²}`; with `ν² = α₀² + ω_cr²` the latter are
  `−α₀ ± jω_cr` (`roots_victim_quadratic`).  The construction takes `D/M` and `ω_c` as the two
  positive roots of `t² − (β₃ + 2α₀)t + (ν² + 2α₀β₃)` and `K = M β₃ ν² / ω_c`.  Consequently
  `T_exact = ω_c K / p(s) = β₃ ν² / ((s + β₃)(s² + 2α₀ s + ν²))` (`Texact_family`).
* `hasDerivAt_log_norm_Texact`: `∂_{β₃} ln |T_exact(2jω)| = 4ω² / [β₃(β₃² + 4ω²)]` (victim pair
  and `ω` held fixed).
* `Modal.exists_root_branch`, `Modal.root_branch_deriv` (`theorem/Modal/Sensitivity.lean`): a
  simple root `λ₀` of `P(s) + c K₀ = 0` (`P'(λ₀) ≠ 0`) continues to a differentiable root branch
  `λ(K)` with `dλ/dK = −c / P'(λ)` (inverse function theorem); for the VSM cubic `c = ω_c`, and
  on the `β₃` family `P'(−α₀ + jω_cr) = 2jMω_cr(β₃ − α₀ + jω_cr)` (`gfm_victim_derivative`).
* `gfm_field_indep_Qref`: with zero reactive-power droop gain (`K_q = m_q = 0`) the internal
  emf of the droop law is `E₀` for either Q-sensing convention, so the VSM + low-pass field does
  not depend on `Q_ref` at all (its Jacobian and spectrum are exactly `Q_ref`-independent).
-/

noncomputable section
namespace powerlib.GFM.ContrastAlgebra
open Filter Topology

/-! ## The `β₃` parameter family -/

/-- `β₃` family: positive `D, K, ω_c` realizing the prescribed spectrum. -/
@[tmio M, powerlib_foundation] theorem beta3_family {α0 ν β3 M : ℝ} (hα : 0 < α0) (hν : 0 < ν)
    (hβ : 2 * (α0 + ν) < β3) (hM : 0 < M) :
    ∃ D K ωc : ℝ, 0 < D ∧ 0 < K ∧ 0 < ωc ∧ ∀ s : ℂ,
      (s + ωc) * (M * s ^ 2 + D * s) + ωc * K =
        M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ν ^ 2)) := by
  set disc := (β3 + 2 * α0) ^ 2 - 4 * (ν ^ 2 + 2 * α0 * β3) with hdisc
  have hdisc' : disc = (β3 - 2 * α0) ^ 2 - 4 * ν ^ 2 := by rw [hdisc]; ring
  have hdpos : 0 < disc := by rw [hdisc']; nlinarith
  set r := Real.sqrt disc with hr
  have hr2 : r ^ 2 = disc := Real.sq_sqrt hdpos.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hβpos : 0 < β3 := by linarith
  have hrlt : r < β3 + 2 * α0 := by
    have : disc < (β3 + 2 * α0) ^ 2 := by
      rw [hdisc]; have : 0 < ν ^ 2 + 2 * α0 * β3 := by positivity
      linarith
    nlinarith
  set tm := (β3 + 2 * α0 - r) / 2
  set tp := (β3 + 2 * α0 + r) / 2
  have htm : 0 < tm := by simp only [tm]; linarith
  have htp : 0 < tp := by simp only [tp]; linarith
  have hsum : tp + tm = β3 + 2 * α0 := by simp only [tp, tm]; ring
  have hprod : tp * tm = ν ^ 2 + 2 * α0 * β3 := by
    simp only [tp, tm]; rw [show (β3 + 2 * α0 + r) / 2 * ((β3 + 2 * α0 - r) / 2) =
      ((β3 + 2 * α0) ^ 2 - r ^ 2) / 4 by ring, hr2, hdisc]; ring
  refine ⟨M * tp, M * β3 * ν ^ 2 / tm, tm, by positivity, by positivity, htm, fun s => ?_⟩
  have hsumC : (tp : ℂ) + tm = β3 + 2 * α0 := by exact_mod_cast hsum
  have hprodC : (tp : ℂ) * tm = ν ^ 2 + 2 * α0 * β3 := by exact_mod_cast hprod
  have htmC : (tm : ℂ) ≠ 0 := by exact_mod_cast htm.ne'
  have hK : (tm : ℂ) * ((M : ℂ) * β3 * ν ^ 2 / tm) = M * β3 * ν ^ 2 := by field_simp
  push_cast
  linear_combination ((M : ℂ) * s ^ 2) * hsumC + ((M : ℂ) * s) * hprodC + hK

/-- `s² + 2α₀ s + (α₀² + ω_cr²) = (s − (−α₀ + jω_cr))(s − (−α₀ − jω_cr))`. -/
@[tmio T, powerlib_foundation] theorem roots_victim_quadratic (α0 ωcr : ℝ) (s : ℂ) :
    s ^ 2 + 2 * α0 * s + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ) =
      (s - (-α0 + Complex.I * ωcr)) * (s - (-α0 - Complex.I * ωcr)) := by
  push_cast
  linear_combination ((ωcr : ℂ) ^ 2) * Complex.I_sq

/-- Spectrum of the family: the roots are exactly `−β₃` and `−α₀ ± jω_cr`. -/
@[powerlib_foundation] theorem family_roots_iff {α0 ωcr β3 M : ℝ} (hM : M ≠ 0) (s : ℂ) :
    M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ))) = 0 ↔
      s = -β3 ∨ s = -α0 + Complex.I * ωcr ∨ s = -α0 - Complex.I * ωcr := by
  rw [roots_victim_quadratic]
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  simp only [mul_eq_zero, hMC, false_or, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- On the family, `T_exact = ω_c K / p(s)` equals `β₃ ν² / ((s + β₃)(s² + 2α₀ s + ν²))`. -/
@[powerlib_foundation] theorem Texact_family {α0 ν β3 M D K ωc : ℝ} (hM : M ≠ 0)
    (hK : ωc * K = M * β3 * ν ^ 2)
    (hfam : ∀ s : ℂ, (s + ωc) * (M * s ^ 2 + D * s) + ωc * K =
      M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ν ^ 2))) (s : ℂ) :
    (ωc * K : ℂ) / ((s + ωc) * (M * s ^ 2 + D * s) + ωc * K) =
      (β3 * ν ^ 2 : ℂ) / ((s + β3) * (s ^ 2 + 2 * α0 * s + ν ^ 2)) := by
  have hKC : (ωc : ℂ) * K = M * (β3 * ν ^ 2) := by
    rw [mul_assoc] at hK; exact_mod_cast hK
  rw [hfam, hKC, mul_div_mul_left _ _ (by exact_mod_cast hM)]

/-! ## Tuning sensitivity of `|T_exact|` -/

/-- `T_exact(s) = β ν² / ((s + β)(s² + 2α₀ s + ν²))`. -/
def Texact (α0 ν β : ℝ) (s : ℂ) : ℂ :=
  ((β * ν ^ 2 : ℝ) : ℂ) / ((s + β) * (s ^ 2 + 2 * α0 * s + ν ^ 2))

/-- `∂_{β₃} ln |T_exact(2jω)| = 4ω² / [β₃(β₃² + 4ω²)]`. -/
@[powerlib_foundation] theorem hasDerivAt_log_norm_Texact {α0 ν ω β : ℝ} (hβ : 0 < β)
    (hν : ν ≠ 0)
    (hq : (2 * Complex.I * ω) ^ 2 + 2 * α0 * (2 * Complex.I * ω) + (ν : ℂ) ^ 2 ≠ 0) :
    HasDerivAt (fun b => Real.log ‖Texact α0 ν b (2 * Complex.I * ω)‖)
      (4 * ω ^ 2 / (β * (β ^ 2 + 4 * ω ^ 2))) β := by
  set q : ℂ := (2 * Complex.I * ω) ^ 2 + 2 * α0 * (2 * Complex.I * ω) + (ν : ℂ) ^ 2
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hnorm : ∀ b : ℝ, 0 < b → ‖(2 * Complex.I * ω + b : ℂ)‖ = Real.sqrt (b ^ 2 + 4 * ω ^ 2) := by
    intro b _
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  let g : ℝ → ℝ := fun b => Real.log b + Real.log (ν ^ 2) - Real.log (b ^ 2 + 4 * ω ^ 2) / 2 -
    Real.log ‖q‖
  have hev : (fun b => Real.log ‖Texact α0 ν b (2 * Complex.I * ω)‖) =ᶠ[𝓝 β] g := by
    filter_upwards [Ioi_mem_nhds hβ] with b hb
    have hb' : (0 : ℝ) < b := hb
    have h4 : 0 < b ^ 2 + 4 * ω ^ 2 := by positivity
    have hn2 : 0 < ν ^ 2 := by positivity
    rw [Texact, norm_div, norm_mul, hnorm b hb', Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hb'.ne' hn2.ne',
      Real.log_mul (Real.sqrt_pos.2 h4).ne' hqn.ne', Real.log_sqrt h4.le]
    simp only [g]
    ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h4 : 0 < β ^ 2 + 4 * ω ^ 2 := by positivity
  have h1 : HasDerivAt (fun b : ℝ => Real.log b) β⁻¹ β := Real.hasDerivAt_log hβ.ne'
  have h2 : HasDerivAt (fun b : ℝ => b ^ 2 + 4 * ω ^ 2) (2 * β) β := by
    simpa using (hasDerivAt_pow 2 β).add_const (4 * ω ^ 2)
  have h3 := h2.log h4.ne'
  have hd := ((h1.add_const (Real.log (ν ^ 2))).sub (h3.div_const 2)).sub_const (Real.log ‖q‖)
  convert hd using 1
  field_simp
  ring

/-! ## Simple-root continuation: `dλ/dK = −c / P'(λ)` -/

/-- VSM cubic on the `β₃` family: `P(s) = (s + ω_c)(M s² + D s)` has
`P'(−α₀ + jω_cr) = 2jMω_cr(β₃ − α₀ + jω_cr)`. -/
@[powerlib_foundation] theorem gfm_victim_derivative {α0 ωcr β3 M D K ωc : ℝ}
    (hfam : ∀ s : ℂ, (s + ωc) * (M * s ^ 2 + D * s) + ωc * K =
      M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ)))) :
    HasStrictDerivAt (fun s : ℂ => (s + ωc) * (M * s ^ 2 + D * s))
      (2 * Complex.I * M * ωcr * (β3 - α0 + Complex.I * ωcr)) (-α0 + Complex.I * ωcr) := by
  set lam : ℂ := -α0 + Complex.I * ωcr
  have hR : HasStrictDerivAt
      (fun s : ℂ => M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ))) -
        ωc * K)
      (M * ((lam ^ 2 + 2 * α0 * lam + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ)) +
        (lam + β3) * (2 * lam + 2 * α0))) lam := by
    have h1 := (hasStrictDerivAt_id lam).add_const (β3 : ℂ)
    have h2 := (((hasStrictDerivAt_id lam).pow 2).add
      ((hasStrictDerivAt_id lam).const_mul (2 * α0 : ℂ))).add_const
      (((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ))
    have h3 : HasStrictDerivAt
        (fun s : ℂ => M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ))) -
          ωc * K) _ lam := ((h1.mul h2).const_mul (M : ℂ)).sub_const ((ωc : ℂ) * K)
    refine h3.congr_deriv ?_
    simp
  have hfun : (fun s : ℂ => (s + ωc) * (M * s ^ 2 + D * s)) =
      fun s : ℂ => M * ((s + β3) * (s ^ 2 + 2 * α0 * s + ((α0 ^ 2 + ωcr ^ 2 : ℝ) : ℂ))) -
        ωc * K := by
    funext s; rw [← hfam s]; ring
  rw [hfun]
  refine hR.congr_deriv ?_
  simp only [lam]
  push_cast
  linear_combination ((M : ℂ) * (ωcr : ℂ) ^ 2) * Complex.I_sq

/-! ## Zero reactive-power droop removes the `Q_ref` channel -/

/-- Internal emf, PCC Q-sensing closed form of the source model. -/
def emfPCC (E0 mq Qref V X δ : ℝ) : ℝ :=
  (E0 + mq * Qref + mq * V ^ 2 / X) / (1 + mq * V * Real.cos δ / X)

/-- Internal-emf Q-sensing: `E` solves `(m_q/X)E² + (1 − m_q V cos δ/X)E − (E₀ + m_q Q_ref) = 0`. -/
def IsEmfInternal (E0 mq Qref V X δ E : ℝ) : Prop :=
  mq / X * E ^ 2 + (1 - mq * V * Real.cos δ / X) * E - (E0 + mq * Qref) = 0

@[powerlib_foundation] theorem emfPCC_zero (E0 Qref V X δ : ℝ) : emfPCC E0 0 Qref V X δ = E0 := by
  simp [emfPCC]

@[powerlib_foundation] theorem isEmfInternal_zero_iff (E0 Qref V X δ E : ℝ) :
    IsEmfInternal E0 0 Qref V X δ E ↔ E = E0 := by
  simp [IsEmfInternal, sub_eq_zero]

/-- VSM + low-pass field `(δ, ω, P_f)` with an emf law `E(δ)`:
`δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (E(δ) V sin δ / X − P_f)`. -/
def gfmField (E : ℝ → ℝ) (M D ωc Pref V X : ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 1, (Pref - y 2 - D * y 1) / M, ωc * (E (y 0) * V * Real.sin (y 0) / X - y 2)]

/-- `K_q = 0`: the field (hence its Jacobian and spectrum at any point) is independent of
`Q_ref`, for the PCC-sensing law; the internal-sensing law has the unique solution `E₀`. -/
@[powerlib_foundation] theorem gfm_field_indep_Qref (E0 M D ωc Pref V X Qref Qref' : ℝ) :
    gfmField (emfPCC E0 0 Qref V X) M D ωc Pref V X =
      gfmField (emfPCC E0 0 Qref' V X) M D ωc Pref V X := by
  funext y
  simp [gfmField, emfPCC_zero]

end powerlib.GFM.ContrastAlgebra
