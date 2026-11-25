import theorem.GridTiedConverter.GFM.PSCFull

/-! # PSC with active damping under grid-voltage amplitude modulation

The four-state PSC core of `PSCFull` with the grid-voltage magnitude as the excitation. The voltage
enters through `φ(δ) = V e^{−jδ}` only: it forces the power filter and both high-pass branches
(`B_V`), and it modulates the stiffness, the branch couplings and the branch inputs (`G_V ≠ 0`).
The forced response, the pump coefficient and its normalized form are derived exactly for the
generic linearized core; for the model the voltage data are the `V`-derivatives of the model
functions, and without active resistance the pump has a closed form that does not vanish at no
load.

Model boundary.
* As `PSCFull.Model`: converter frame, quasi-static network, PCC power, high-pass active resistance
  `(ℓ, ℓ̄)`, coordinates `(δ, p_f, ℓ, ℓ̄)` with complexified functions. The grid voltage `V` is
  varied through `withV`; all partial derivatives in `V` are taken at fixed states `(δ, ℓ, ℓ̄)`.
* The pump is evaluated with the conventions of `PSCFull` (`pumpc`, eigenvectors `left`, `right`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (PSC core), §5.5 and (24) (angle pump); the voltage excitation
is new.

Results (generic core, `Coeffs` with the voltage data `VIn`).
* `Bv`, `GV`, `forcedV_eq` — `(sI − J) z_V = B_V` with `z_δ = −k ω_f K_V(s)/D(s)`,
  `K_V = P_V + P_ℓ c_V + P_ℓ̄ c̃_V`.
* `pumpV_eq` — `g_V = u_{p_f} ω_f v G_V(s₁, s₂, λ)` with the exact bracket `GVb`;
  `GVb_plain` — without the branch in the power, `G_V = P_δV − k ω_f P_V P_δδ/D(s₁)`;
  `normalizedPumpV_eq` — `ĝ_V = |c_D| |v| |G_V|/|K_r|` (the angle form with `|z_δ||G|` replaced).

Results (the model).
* `hasDerivAt_φ_V`, `hasDerivAt_cur_V`, `hasDerivAt_curt_V`, `hasDerivAt_curδ_V`,
  `hasDerivAt_curtδ_V`, `hasDerivAt_pw_V`, `hasDerivAt_pwδ_V`, `hasDerivAt_pwℓ_V`,
  `hasDerivAt_pwm_V` — the voltage data `vin` are the `V`-derivatives of the model functions;
  `hasDerivAt_field_V` — `∂f/∂V` of the field.
* `plain_of_ra`, `GVb_ra` — with `r_a = 0` the branch leaves the power row:
  `G_V = P_δV − k ω_f P_V P_δδ/D(s₁)`.
* `vin_lossless` — `R_f = R_g = r_a = 0`: `P_V = E sin δ₀/X`, `P_δV = E cos δ₀/X`;
  `pumpV_lossless` — `g_V = u_{p_f} ω_f v (E/X)(cos δ₀ + k ω_f V E sin² δ₀/(X D(s₁)))`;
  `pumpV_noload` — `δ₀ = 0`: `g_V = u_{p_f} ω_f v E/X ≠ 0`, whereas the angle pump of this core
  vanishes with `P_δδ`.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the PSC core (input, modulation, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace PSCFull
open Complex ComplexConjugate Matrix

/-- The voltage data of the linearized PSC core: the voltage input of the power and of the two
high-pass branches (`P_V`, `e_V`, `ē_V`) and the voltage derivatives of the modulable Jacobian
entries (`a_V`, `ā_V`, `P_δV`, `P_ℓV`, `P_ℓ̄V`). -/
structure VIn where
  PV : ℂ
  eV : ℂ
  emV : ℂ
  aV : ℂ
  abV : ℂ
  PδV : ℂ
  PℓV : ℂ
  PmV : ℂ

namespace Coeffs

variable (q : Coeffs) (w : VIn)

/-- The voltage input `B_V = ∂f/∂V`. -/
def Bv : Fin 4 → ℂ := ![0, q.ωf * w.PV, q.αd * w.eV, q.αd * w.emV]

/-- The direct voltage modulation `G_V = ∂J/∂V`. -/
def GV : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
    q.ωf * w.PδV, 0, q.ωf * w.PℓV, q.ωf * w.PmV;
    q.αd * w.aV, 0, 0, 0;
    q.αd * w.abV, 0, 0, 0]

/-- The voltage-driven parts of the two branches. -/
def cV (s : ℂ) : ℂ := q.αd * w.eV / (s + q.αd * (1 - q.b))
def ctV (s : ℂ) : ℂ := q.αd * w.emV / (s + q.αd * (1 - q.bb))

/-- The voltage transfer to the power, `K_V(s) = P_V + P_ℓ c_V(s) + P_ℓ̄ c̃_V(s)`. -/
def KV (s : ℂ) : ℂ := w.PV + q.Pℓ * q.cV w s + q.Pm * q.ctV w s

/-- The angle response to the voltage, `z_δ = −k ω_f K_V(s)/D(s)`. -/
def forcedVδ (s : ℂ) : ℂ := -(q.k * q.ωf * q.KV w s) / q.D s

/-- The forced response to `V̂ = 1` at `s`. -/
def forcedV (s : ℂ) : Fin 4 → ℂ :=
  ![q.forcedVδ w s, -s * q.forcedVδ w s / q.k, q.c s * q.forcedVδ w s + q.cV w s,
    q.ct s * q.forcedVδ w s + q.ctV w s]

/-- The bracket of the voltage pump coefficient. -/
def GVb (s1 s2 lam : ℂ) : ℂ :=
  q.forcedVδ w s1 * q.G s1 s2 lam + q.Pδℓ * q.cV w s1 + q.Pδm * q.ctV w s1 +
    q.Pℓm * (q.ctV w s1 * q.c s2 + q.cV w s1 * q.ct s2) +
    w.PδV + w.PℓV * q.c s2 + w.PmV * q.ct s2 +
    q.Pℓ * q.αd * w.aV / (lam + q.αd * (1 - q.b)) + q.Pm * q.αd * w.abV / (lam + q.αd * (1 - q.bb))

variable {q}

/-- `(sI − J) z_V = B_V`. -/
@[tmio T, powerlib_foundation] theorem forcedV_eq {s : ℂ} (hk : q.k ≠ 0) (hD : q.D s ≠ 0)
    (h1 : s + q.αd * (1 - q.b) ≠ 0) (h2 : s + q.αd * (1 - q.bb) ≠ 0) :
    (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - q.J) *ᵥ q.forcedV w s = q.Bv w := by
  have e1 := c_mul h1
  have e2 := ct_mul h2
  have f1 : q.cV w s * (s + q.αd * (1 - q.b)) = q.αd * w.eV := by simp only [cV]; field_simp
  have f2 : q.ctV w s * (s + q.αd * (1 - q.bb)) = q.αd * w.emV := by simp only [ctV]; field_simp
  have key : q.forcedVδ w s * q.D s = -(q.k * q.ωf * q.KV w s) := by
    simp only [forcedVδ]; field_simp
  have hDdef : q.D s = s * (s + q.ωf) + q.k * q.ωf * q.K s := rfl
  have hKdef : q.K s = q.Pδ + q.Pℓ * q.c s + q.Pm * q.ct s := rfl
  have hKV : q.KV w s = w.PV + q.Pℓ * q.cV w s + q.Pm * q.ctV w s := rfl
  funext i
  fin_cases i
  · simp [J, forcedV, Bv, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    field_simp
    ring
  · simp [J, forcedV, Bv, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    rw [hDdef, hKdef, hKV] at key
    field_simp
    linear_combination (-1 : ℂ) * key
  · simp [J, forcedV, Bv, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    linear_combination (q.forcedVδ w s) * e1 + f1
  · simp [J, forcedV, Bv, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    linear_combination (q.forcedVδ w s) * e2 + f2

/-- The voltage pump: for a voltage modulation of amplitude `v` (forced response `v z_V(s₁)` and
direct modulation `v G_V`), `g_V = u_{p_f} ω_f v G_V(s₁, s₂, λ)` with
`G_V = z_{δV} G + P_δℓ c_V + P_δℓ̄ c̃_V + P_ℓℓ̄(c̃_V c₂ + c_V c̃₂) + P_δV + P_ℓV c₂ + P_ℓ̄V c̃₂
+ P_ℓ α_d a_V/(λ + α_d(1 − b)) + P_ℓ̄ α_d ā_V/(λ + α_d(1 − b̄))`. -/
@[tmio T, powerlib_foundation] theorem pumpV_eq (s1 s2 lam v : ℂ) :
    pumpc (q.A1 (v • q.forcedV w s1) + v • q.GV w) (q.left lam) (q.right s2) =
      (-q.k / q.Dd lam) * q.ωf * v * q.GVb w s1 s2 lam := by
  simp only [pumpc, A1, GV, forcedV, left, right, GVb, G, c, ct, cV, ctV, mulVec, dotProduct,
    Fin.sum_univ_four]
  simp
  ring

/-- Without the high-pass branch in the power (`P_ℓ = P_ℓ̄ = P_δℓ = P_δℓ̄ = P_ℓℓ̄ = 0`,
`P_ℓV = P_ℓ̄V = 0`, e.g. `r_a = 0`) the bracket is the second-order form
`G_V = P_δV − k ω_f P_V P_δδ/D(s₁)`. -/
@[tmio T, powerlib_foundation] theorem GVb_plain (h1 : q.Pℓ = 0) (h2 : q.Pm = 0)
    (h3 : q.Pδℓ = 0) (h4 : q.Pδm = 0) (h5 : q.Pℓm = 0) (h6 : w.PℓV = 0) (h7 : w.PmV = 0)
    (s1 s2 lam : ℂ) :
    q.GVb w s1 s2 lam = w.PδV - q.k * q.ωf * w.PV * q.Pδδ / q.D s1 := by
  simp only [GVb, G, forcedVδ, KV, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- The exact normalized voltage pump `ĝ_V = 2|g_V|/Ω = |c_D| |v| |G_V|/|K_r|`, the same form as
the angle pump (`normalizedPump_eq`) with `|z_δ| |G|` replaced by `|v| |G_V|`. -/
@[tmio T, powerlib_foundation] theorem normalizedPumpV_eq (lam ω v : ℂ) (hΩ : 0 < lam.im)
    (hDd : q.Dd lam ≠ 0) (hkω : q.k * q.ωf ≠ 0) :
    ParametricResonance.Element.normalizedPump
        (pumpc (q.A1 (v • q.forcedV w ω) + v • q.GV w) (q.left lam) (q.right (conj lam)))
        lam.im =
      ‖2 * I * (lam.im : ℂ) / q.Dd lam‖ * ‖v‖ * ‖q.GVb w ω (conj lam) lam‖ /
        ‖(lam.im : ℂ) ^ 2 / (q.k * q.ωf)‖ := by
  have hΩc : (lam.im : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  rw [ParametricResonance.Element.normalizedPump, pumpV_eq, upf_eq lam hΩc hDd]
  have hK : ‖(lam.im : ℂ) ^ 2 / (q.k * q.ωf)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact div_ne_zero (pow_ne_zero _ hΩc) hkω
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hΩ, h2] at hK ⊢
  field_simp

end Coeffs

/-! ## The voltage derivatives of the model -/

namespace Model

variable (p : Model)

/-- The model with the grid-voltage magnitude replaced by `V'`. -/
def withV (V' : ℝ) : Model := { p with V := V' }

/-- `∂φ/∂V = e^{−jδ}`, `∂φ̃/∂V = e^{jδ}`. -/
def eφ (δ : ℂ) : ℂ := exp (-(δ * I))
def eφt (δ : ℂ) : ℂ := exp (δ * I)

def curV (δ : ℂ) : ℂ := -eφ δ / p.Z
def curtV (δ : ℂ) : ℂ := -eφt δ / p.Zc
def curδV (δ : ℂ) : ℂ := I * eφ δ / p.Z
def curtδV (δ : ℂ) : ℂ := -I * eφt δ / p.Zc
def pwV (δ ℓ m : ℂ) : ℂ :=
  (eφ δ * p.curt δ m + p.φ δ * p.curtV δ + eφt δ * p.cur δ ℓ + p.φt δ * p.curV δ) / 2 +
    p.Rg * (p.curV δ * p.curt δ m + p.cur δ ℓ * p.curtV δ)
def pwδV (δ ℓ m : ℂ) : ℂ :=
  ((-I * eφ δ) * p.curt δ m + (-I * p.φ δ) * p.curtV δ + eφ δ * p.curtδ δ + p.φ δ * p.curtδV δ +
    (I * eφt δ) * p.cur δ ℓ + (I * p.φt δ) * p.curV δ + eφt δ * p.curδ δ +
    p.φt δ * p.curδV δ) / 2 +
    p.Rg * (p.curδV δ * p.curt δ m + p.curδ δ * p.curtV δ + p.curV δ * p.curtδ δ +
      p.cur δ ℓ * p.curtδV δ)
def pwℓV (δ : ℂ) : ℂ := eφt δ * (p.ra / p.Z) / 2 + p.Rg * (p.ra / p.Z) * p.curtV δ
def pwmV (δ : ℂ) : ℂ := eφ δ * (p.ra / p.Zc) / 2 + p.Rg * p.curV δ * (p.ra / p.Zc)

section VDeriv

variable (δ ℓ m : ℂ) (V0 : ℝ)

@[tmio M, powerlib_domain] theorem hasDerivAt_φ_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').φ δ) (eφ δ) V0 := by
  have h := ((hasDerivAt_id V0).ofReal_comp).mul_const (exp (-(δ * I)))
  convert h using 1
  · funext V'; simp [withV, φ]
  · simp [eφ]

@[tmio M, powerlib_domain] theorem hasDerivAt_φt_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').φt δ) (eφt δ) V0 := by
  have h := ((hasDerivAt_id V0).ofReal_comp).mul_const (exp (δ * I))
  convert h using 1
  · funext V'; simp [withV, φt]
  · simp [eφt]

@[tmio M, powerlib_domain] theorem hasDerivAt_cur_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').cur δ ℓ) (p.curV δ) V0 := by
  have h := ((p.hasDerivAt_φ_V δ V0).const_sub ((p.E : ℂ) + p.ra * ℓ)).div_const p.Z
  convert h using 1
  · funext V'; rfl
  · rfl

@[tmio M, powerlib_domain] theorem hasDerivAt_curt_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').curt δ m) (p.curtV δ) V0 := by
  have h := ((p.hasDerivAt_φt_V δ V0).const_sub ((p.E : ℂ) + p.ra * m)).div_const p.Zc
  convert h using 1
  · funext V'; rfl
  · rfl

@[tmio M, powerlib_domain] theorem hasDerivAt_curδ_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').curδ δ) (p.curδV δ) V0 := by
  have h := ((p.hasDerivAt_φ_V δ V0).const_mul I).div_const p.Z
  convert h using 1
  · funext V'; rfl
  · rfl

@[tmio M, powerlib_domain] theorem hasDerivAt_curtδ_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').curtδ δ) (p.curtδV δ) V0 := by
  have h := ((p.hasDerivAt_φt_V δ V0).const_mul (-I)).div_const p.Zc
  convert h using 1
  · funext V'; rfl
  · rfl

@[tmio M, powerlib_domain] theorem withV_self : p.withV p.V = p := rfl

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').pw δ ℓ m) (p.pwV δ ℓ m) p.V := by
  have h := ((((p.hasDerivAt_φ_V δ p.V).mul (p.hasDerivAt_curt_V δ m p.V)).add
    ((p.hasDerivAt_φt_V δ p.V).mul (p.hasDerivAt_cur_V δ ℓ p.V))).div_const 2).add
    (((p.hasDerivAt_cur_V δ ℓ p.V).mul (p.hasDerivAt_curt_V δ m p.V)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext V'
    have hRg : ((p.withV V').Rg : ℂ) = p.Rg := rfl
    simp only [Pi.add_apply, Pi.mul_apply]; rw [pw_eq, hRg]; ring
  · simp only [pwV, withV_self]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pwδ_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').pwδ δ ℓ m) (p.pwδV δ ℓ m) p.V := by
  have hφ := p.hasDerivAt_φ_V δ p.V
  have hφt := p.hasDerivAt_φt_V δ p.V
  have hc := p.hasDerivAt_cur_V δ ℓ p.V
  have hct := p.hasDerivAt_curt_V δ m p.V
  have hd := p.hasDerivAt_curδ_V δ p.V
  have hdt := p.hasDerivAt_curtδ_V δ p.V
  have h := ((((((hφ.const_mul (-I)).mul hct).add (hφ.mul hdt)).add ((hφt.const_mul I).mul hc)).add
    (hφt.mul hd)).div_const 2).add
    ((((hd.mul hct).add (hc.mul hdt))).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext V'; simp only [Pi.add_apply, Pi.mul_apply]; rfl
  · simp only [pwδV, withV_self]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pwℓ_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').pwℓ δ m) (p.pwℓV δ) V0 := by
  have h := (((p.hasDerivAt_φt_V δ V0).mul_const (p.ra / p.Z)).div_const 2).add
    ((p.hasDerivAt_curt_V δ m V0).const_mul ((p.Rg : ℂ) * (p.ra / p.Z)))
  convert h using 1
  · funext V'; rfl
  · rfl

@[tmio M, powerlib_domain] theorem hasDerivAt_pwm_V :
    HasDerivAt (fun V' : ℝ => (p.withV V').pwm δ ℓ) (p.pwmV δ) V0 := by
  have h := (((p.hasDerivAt_φ_V δ V0).mul_const (p.ra / p.Zc)).div_const 2).add
    (((p.hasDerivAt_cur_V δ ℓ V0).mul_const (p.ra / p.Zc)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext V'
    have hRg : ((p.withV V').Rg : ℂ) = p.Rg := rfl
    have hra : ((p.withV V').ra : ℂ) = p.ra := rfl
    have hZc : (p.withV V').Zc = p.Zc := rfl
    simp only [Pi.add_apply, pwm, hRg, hra, hZc]; ring
  · simp only [pwmV]; ring

end VDeriv

/-- The voltage data of the model at the equilibrium angle `δ₀` (states `ℓ₀`, `ℓ̄₀`). -/
def vin (δ0 : ℂ) : VIn where
  PV := p.pwV δ0 (p.ell0 δ0) (p.m0 δ0)
  eV := p.curV δ0
  emV := p.curtV δ0
  aV := p.curδV δ0
  abV := p.curtδV δ0
  PδV := p.pwδV δ0 (p.ell0 δ0) (p.m0 δ0)
  PℓV := p.pwℓV δ0
  PmV := p.pwmV δ0

/-- `∂f/∂V`: the voltage enters the power filter and both high-pass branches, not the angle;
at the equilibrium this is `B_V` of `vin`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_field_V (θd Pref : ℝ) (x : Fin 4 → ℂ) :
    HasDerivAt (fun V' : ℝ => (p.withV V').field θd Pref x 1) (p.ωf * p.pwV (x 0) (x 2) (x 3)) p.V ∧
      HasDerivAt (fun V' : ℝ => (p.withV V').field θd Pref x 2) (p.αd * p.curV (x 0)) p.V ∧
      HasDerivAt (fun V' : ℝ => (p.withV V').field θd Pref x 3) (p.αd * p.curtV (x 0)) p.V := by
  refine ⟨?_, ?_, ?_⟩
  · have h := ((p.hasDerivAt_pw_V (x 0) (x 2) (x 3)).sub_const (x 1)).const_mul (p.ωf : ℂ)
    convert h using 1
    funext V'; rfl
  · have h := ((p.hasDerivAt_cur_V (x 0) (x 2) p.V).sub_const (x 2)).const_mul (p.αd : ℂ)
    convert h using 1
    funext V'; rfl
  · have h := ((p.hasDerivAt_curt_V (x 0) (x 3) p.V).sub_const (x 3)).const_mul (p.αd : ℂ)
    convert h using 1
    funext V'; rfl

/-- Without the active resistance (`r_a = 0`) the high-pass branch leaves the power row, for the
angle and for the voltage. -/
@[tmio M, powerlib_domain] theorem plain_of_ra (δ0 : ℂ) (hra : p.ra = 0) :
    (p.coeffs δ0).Pℓ = 0 ∧ (p.coeffs δ0).Pm = 0 ∧ (p.coeffs δ0).Pδℓ = 0 ∧
      (p.coeffs δ0).Pδm = 0 ∧ (p.coeffs δ0).Pℓm = 0 ∧ (p.vin δ0).PℓV = 0 ∧
      (p.vin δ0).PmV = 0 := by
  simp [coeffs, vin, pwℓ, pwm, pwδℓ, pwδm, pwℓm, pwℓV, pwmV, hra]

/-- `r_a = 0`: `G_V = P_δV − k ω_f P_V P_δδ/D(s₁)`. -/
@[tmio M, powerlib_domain] theorem GVb_ra (δ0 : ℂ) (hra : p.ra = 0) (s1 s2 lam : ℂ) :
    (p.coeffs δ0).GVb (p.vin δ0) s1 s2 lam =
      (p.vin δ0).PδV - p.k * p.ωf * (p.vin δ0).PV * (p.coeffs δ0).Pδδ / (p.coeffs δ0).D s1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := p.plain_of_ra δ0 hra
  rw [Coeffs.GVb_plain _ h1 h2 h3 h4 h5 h6 h7]
  rfl

/-- Lossless, no active resistance (`R_f = R_g = r_a = 0`): `P_V = E sin δ₀/X`,
`P_δV = E cos δ₀/X`. -/
@[tmio M, powerlib_domain] theorem vin_lossless (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0)
    (hra : p.ra = 0) (hX : p.X ≠ 0) :
    (p.vin δ0).PV = ((p.E * Real.sin δ0 / p.X : ℝ) : ℂ) ∧
      (p.vin δ0).PδV = ((p.E * Real.cos δ0 / p.X : ℝ) : ℂ) := by
  have hZ : p.Z = (p.X : ℂ) * I := by simp [Z, hRf, hRg, hra]
  have hZc : p.Zc = -((p.X : ℂ) * I) := by simp [Zc, hRf, hRg, hra]
  have he : eφ δ0 = (Real.cos δ0 : ℂ) - Real.sin δ0 * I := by
    simp only [eφ]; rw [PSCActiveDamping.exp_neg_mul_I]
  have het : eφt δ0 = (Real.cos δ0 : ℂ) + Real.sin δ0 * I := by
    simp only [eφt]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hφ : p.φ δ0 = p.V * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
    simp only [φ]; rw [PSCActiveDamping.exp_neg_mul_I]
  have hφt : p.φt δ0 = p.V * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) := by
    simp only [φt]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  constructor
  · simp only [vin, pwV, curV, curtV, cur, curt, hZ, hZc, he, het, hφ, hφt, hRg, hra]
    generalize Real.cos δ0 = c at *
    generalize Real.sin δ0 = sn at *
    push_cast
    field_simp
    ring_nf
  · simp only [vin, pwδV, curV, curtV, curδV, curtδV, cur, curt, curδ, curtδ, hZ, hZc, he, het,
      hφ, hφt, hRg, hra]
    generalize Real.cos δ0 = c at *
    generalize Real.sin δ0 = sn at *
    push_cast
    field_simp
    ring_nf

/-- The voltage pump of the lossless core without active resistance
(`R_f = R_g = r_a = 0`): `g_V = u_{p_f} ω_f v (E/X)(cos δ₀ + k ω_f V E sin²δ₀/(X D(s₁)))`,
`D(s) = s(s + ω_f) + k ω_f V E cos δ₀/X`. -/
@[tmio M, powerlib_domain] theorem pumpV_lossless (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0)
    (hra : p.ra = 0) (hX : p.X ≠ 0) (s1 s2 lam v : ℂ) :
    pumpc ((p.coeffs δ0).A1 (v • (p.coeffs δ0).forcedV (p.vin δ0) s1) +
        v • (p.coeffs δ0).GV (p.vin δ0)) ((p.coeffs δ0).left lam) ((p.coeffs δ0).right s2) =
      (-p.k / (p.coeffs δ0).Dd lam) * p.ωf * v * (p.E / p.X) *
        (Real.cos δ0 + p.k * p.ωf * p.V * p.E * Real.sin δ0 ^ 2 / p.X /
          (s1 * (s1 + p.ωf) + p.k * p.ωf * (p.V * p.E * Real.cos δ0 / p.X))) := by
  rw [Coeffs.pumpV_eq, p.GVb_ra δ0 hra]
  obtain ⟨hPV, hPδV⟩ := p.vin_lossless δ0 hRf hRg hra hX
  obtain ⟨hPδδ, hPδ⟩ := p.curvature_lossless δ0 hRf hRg hX
  obtain ⟨h1, h2, -, -, -, -, -⟩ := p.plain_of_ra δ0 hra
  have hD : (p.coeffs δ0).D s1 = s1 * (s1 + p.ωf) + p.k * p.ωf * (p.V * p.E * Real.cos δ0 / p.X) := by
    simp only [Coeffs.D, Coeffs.K, h1, h2, zero_mul, add_zero, hPδ, hra]
    simp
    rfl
  rw [hPV, hPδV, hPδδ, hD, hra]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hk : (p.coeffs δ0).k = p.k := rfl
  have hω : (p.coeffs δ0).ωf = p.ωf := rfl
  rw [hk, hω]
  push_cast
  ring

/-- No load (`δ₀ = 0`): the angle input does not pump through `P_δδ` (`P_δδ = 0`), but the voltage
still does: `g_V = u_{p_f} ω_f v E/X ≠ 0`. -/
@[tmio M, powerlib_domain] theorem pumpV_noload (hRf : p.Rf = 0) (hRg : p.Rg = 0)
    (hra : p.ra = 0) (hX : p.X ≠ 0) (s1 s2 lam v : ℂ) :
    pumpc ((p.coeffs 0).A1 (v • (p.coeffs 0).forcedV (p.vin 0) s1) +
        v • (p.coeffs 0).GV (p.vin 0)) ((p.coeffs 0).left lam) ((p.coeffs 0).right s2) =
      (-p.k / (p.coeffs 0).Dd lam) * p.ωf * v * (p.E / p.X) := by
  have h := p.pumpV_lossless 0 hRf hRg hra hX s1 s2 lam v
  simp only [Real.cos_zero, Real.sin_zero, ofReal_zero, ofReal_one] at h
  rw [h]
  ring

end Model
end PSCFull
end powerlib.GFM
