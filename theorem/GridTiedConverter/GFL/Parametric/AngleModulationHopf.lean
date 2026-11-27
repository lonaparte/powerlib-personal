import theorem.GridTiedConverter.GFL.Parametric.AngleModulation
import theorem.Criteria.Hurwitz2
import theorem.ParametricResonance.SmoothOrbitStability

/-! # GFL converter under a 2:1 grid-angle variation: explicit Hopf conditions and Floquet multipliers

`GFL.Parametric.AngleModulation` gives the forced response, `A₁(ω_p)` and the modal contributions of
the grid-following converter. Here the selected DVC mode is placed at a Hopf point of `A₀`,
`λ = ±jΩ`, with the decay and detuning of the source entering at order `ε` through `εA₀'`. This is
the distinguished limit in which the source's first-order averaging (pp. 26–27) is exact. Under
the drive `θ_g = θ_{g0} + ε cos 2Ωt`, the end-to-end theorems give the Floquet multipliers of the
actual forced orbit:
* `|g_m/2| < |λ₁|` (`λ₁ = l A₀' r`) gives stability;
* `|λ₁| < |g_m/2|` gives parametric instability.

All eigen-data are explicit:
* the right eigenvector `r(s) = (1, s/(k_p s + k_i), sA₃₁/L_dc(s), A₃₁/L_dc(s))`;
* the left eigenvector `l(s)`, normalized by `s L_dc(s)/D'(s)`;
* every eigenvalue is a root of `D_GFL`;
* under the Hopf conditions, `D_GFL(s) = (s² + Ω²)(s² + a₃ s + a₂ − Ω²)`.

Model boundary.
* The field `afield` of `GFL.Parametric.AngleModulation` at the operating point
  (`V₀ sin δ₀ = X_g i_{d0}`), in the absolute PLL angle. `shift_solution` carries the orbit back
  to `δ = θ_PLL − θ_g`; `matX_afield` identifies the variational matrices.
* Explicit conditions:
  * the Hopf conditions `a₁ = a₃Ω²` and `a₀ = (a₂ − Ω²)Ω²`;
  * `a₃ > 0` and `a₂ > Ω²`;
  * `L_dc(jΩ) ≠ 0` (automatic with coupling, `Ldc_ne_of_Dg`), `k_{i,PLL} ≠ 0` and `C ≠ 0`.
* The damping and detuning of order `ε` are a constant real `A₀'` (`SmoothForcedOrbit`).

Source: slides "Hidden Instability of Grid-Following Converters Under Small Grid Angle
Variations" (KTH, 2026-11-27), pp. 19–27, 30.

Results.
* `gright`, `glv`, `Dgd`, `gleft`, `hasDerivAt_Dg`, `gright_res`, `gright_eig`, `glv_res`,
  `gleft_eig`, `glv_gright`, `gleft_gright` — the eigenvectors and `l r = 1`.
* `geig_Dg`, `geig_span`, `Dg_factor`, `ghopf_facts`, `geig_stable`, `Ldc_ne_of_Dg`, `gspectral` —
  the spectrum at the Hopf point.
* `orbit_gfl_hopf_stable`, `orbit_gfl_hopf_unstable`, `orbit_gfl_hopf_exp_stable` — end-to-end,
  with the pump `g_m = l A₁(z⁽¹⁾(2jΩ)) r̄` of the source in closed form (`gA1`, `zc`).

Corrections.
None.

Family and connection conclusions.
None: static evidence on the GFL model under grid-angle variation.
-/

noncomputable section
namespace powerlib.GFL.Parametric.AngleModulation
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (matX smJ)

namespace Params
variable (p : Params)

/-! ### Eigenvectors of `A₀` -/

/-- The right eigenvector `r(s) = (1, s/(k_p s + k_i), sA₃₁/L_dc(s), A₃₁/L_dc(s))`. -/
def gright (s : ℂ) : Fin 4 → ℂ :=
  ![1, s / (p.kp * s + p.ki), s * p.A31 / p.Ldc s, p.A31 / p.Ldc s]

/-- The unnormalized left eigenvector `(1, k_i/s, u₃, u₄)`. -/
def glv (s : ℂ) : Fin 4 → ℂ :=
  ![1, p.ki / s, p.Xg * (p.kp * s + p.ki) / s * (p.kpv * s + p.kiv) / p.Ldc s,
    (p.kiv * (p.Xg * (p.kp * s + p.ki) / s) - 3 * p.vd0 * p.kiv / (2 * p.C) *
      (p.Xg * (p.kp * s + p.ki) / s * (p.kpv * s + p.kiv) / p.Ldc s)) / s]

/-- The derivative `D'_GFL(s)`. -/
def Dgd (s : ℂ) : ℂ := 4 * s ^ 3 + 3 * p.da3 * s ^ 2 + 2 * p.da2 * s + p.da1

/-- The left eigenvector normalized by `l r = 1`: `(s L_dc(s)/D'(s)) (1, k_i/s, u₃, u₄)`. -/
def gleft (s : ℂ) : Fin 4 → ℂ := (s * p.Ldc s / p.Dgd s) • p.glv s

@[tmio M, powerlib_domain] theorem hasDerivAt_Dg (s : ℂ) : HasDerivAt p.Dg (p.Dgd s) s := by
  have e : p.Dg = fun s => s ^ 4 + (p.da3 : ℂ) * s ^ 3 + p.da2 * s ^ 2 + p.da1 * s + p.da0 :=
    funext p.Dg_eq
  rw [e]
  have h := (((((hasDerivAt_pow 4 s).add ((hasDerivAt_pow 3 s).const_mul (p.da3 : ℂ))).add
    ((hasDerivAt_pow 2 s).const_mul (p.da2 : ℂ))).add ((hasDerivAt_id' s).const_mul
      (p.da1 : ℂ))).add_const (p.da0 : ℂ))
  convert h using 1
  simp [Dgd]
  ring

/-- Off the characteristic polynomial, `A₀ r − s r = −D(s)/((k_p s + k_i)L_dc(s)) (k_p, 1, 0, 0)`. -/
@[tmio M, powerlib_domain] theorem gright_res {s : ℂ} (hC : p.C ≠ 0)
    (hk : (p.kp : ℂ) * s + p.ki ≠ 0) (hL : p.Ldc s ≠ 0) :
    p.A0.map (algebraMap ℝ ℂ) *ᵥ p.gright s =
      s • p.gright s + (-(p.Dg s) / ((p.kp * s + p.ki) * p.Ldc s)) • ![(p.kp : ℂ), 1, 0, 0] := by
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hk' : s * p.kp + p.ki ≠ 0 := by rw [mul_comm]; exact hk
  funext i
  fin_cases i <;> simp [A0, gright, mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp <;>
    simp only [Dg, Ldc, Gam, A31] <;> push_cast <;> field_simp <;> ring

@[tmio M, powerlib_domain] theorem gright_eig {s : ℂ} (hC : p.C ≠ 0)
    (hk : (p.kp : ℂ) * s + p.ki ≠ 0) (hL : p.Ldc s ≠ 0) (hD : p.Dg s = 0) :
    p.A0.map (algebraMap ℝ ℂ) *ᵥ p.gright s = s • p.gright s := by
  rw [p.gright_res hC hk hL, hD, neg_zero, zero_div, zero_smul, add_zero]

@[tmio M, powerlib_domain] theorem glv_res {s : ℂ} (hC : p.C ≠ 0) (hs : s ≠ 0)
    (hL : p.Ldc s ≠ 0) :
    p.glv s ᵥ* p.A0.map (algebraMap ℝ ℂ) =
      s • p.glv s + (-(p.Dg s) / (s * p.Ldc s)) • ![(1 : ℂ), 0, 0, 0] := by
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  funext j
  fin_cases j <;> simp [A0, glv, vecMul, dotProduct, Fin.sum_univ_four] <;> field_simp <;>
    simp only [Dg, Ldc, Gam, A31] <;> push_cast <;> field_simp <;> ring

@[tmio M, powerlib_domain] theorem gleft_eig {s : ℂ} (hC : p.C ≠ 0) (hs : s ≠ 0)
    (hL : p.Ldc s ≠ 0) (hD : p.Dg s = 0) :
    p.gleft s ᵥ* p.A0.map (algebraMap ℝ ℂ) = s • p.gleft s := by
  rw [gleft, Matrix.smul_vecMul, p.glv_res hC hs hL, hD, neg_zero, zero_div, zero_smul, add_zero,
    smul_comm]

@[tmio M, powerlib_domain] theorem glv_gright {s : ℂ} (hC : p.C ≠ 0) (hs : s ≠ 0)
    (hk : (p.kp : ℂ) * s + p.ki ≠ 0) (hL : p.Ldc s ≠ 0) (hD : p.Dg s = 0) :
    p.glv s ⬝ᵥ p.gright s = p.Dgd s / (s * p.Ldc s) := by
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hk' : s * p.kp + p.ki ≠ 0 := by rw [mul_comm]; exact hk
  simp [glv, gright, dotProduct, Fin.sum_univ_four]
  linear_combination (norm := skip) (-(p.kp * p.Ldc s + (p.kp * s + p.ki) *
    (2 * s + 3 * p.vd0 / (2 * p.C) * (p.kpv - p.id0))) / ((p.kp * s + p.ki) * p.Ldc s) /
      (s * p.Ldc s)) * hD
  field_simp
  simp only [Dg, Dgd, Ldc, Gam, A31, da3, da2, da1]
  push_cast
  field_simp
  ring

@[tmio M, powerlib_domain] theorem gleft_gright {s : ℂ} (hC : p.C ≠ 0) (hs : s ≠ 0)
    (hk : (p.kp : ℂ) * s + p.ki ≠ 0) (hL : p.Ldc s ≠ 0) (hD : p.Dg s = 0) (hd : p.Dgd s ≠ 0) :
    p.gleft s ⬝ᵥ p.gright s = 1 := by
  rw [gleft, smul_dotProduct, p.glv_gright hC hs hk hL hD, smul_eq_mul]
  field_simp

/-! ### Spectrum -/

/-- Every eigenvalue of `A₀` is a root of `D_GFL`. -/
@[tmio M, powerlib_domain] theorem geig_Dg {μ : ℂ} {v : Fin 4 → ℂ} (hv : v ≠ 0)
    (he : p.A0.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) : p.Dg μ = 0 := by
  rw [← p.det_sub_A0]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, sub_self]

/-- Where `k_p s + k_i ≠ 0`, `L_dc(s) ≠ 0`, the eigenspace of `s` is spanned by `r(s)`. -/
@[tmio M, powerlib_domain] theorem geig_span {s : ℂ} (hC : p.C ≠ 0)
    (hk : (p.kp : ℂ) * s + p.ki ≠ 0) (hL : p.Ldc s ≠ 0) {v : Fin 4 → ℂ}
    (he : p.A0.map (algebraMap ℝ ℂ) *ᵥ v = s • v) : v = v 0 • p.gright s := by
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hk' : s * p.kp + p.ki ≠ 0 := by rw [mul_comm]; exact hk
  have e : ∀ i, (p.A0.map (algebraMap ℝ ℂ) *ᵥ v) i = s * v i := fun i => by rw [he]; rfl
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  simp [A0, mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
  have h3 : v 3 = v 0 * (p.A31 / p.Ldc s) := by
    linear_combination (norm := skip) (-1 / p.Ldc s) * e2 -
      ((s + 3 * p.vd0 * (p.kpv - p.id0) / (2 * p.C)) / p.Ldc s) * e3
    field_simp
    simp only [Ldc, A31]
    push_cast
    field_simp
    ring
  have h1 : v 1 = v 0 * (s / (p.kp * s + p.ki)) := by
    field_simp
    linear_combination e0 - p.kp * e1
  funext i
  fin_cases i
  · simp [gright]
  · simp [gright, h1]
  · simp [gright]
    rw [e3, h3]
    ring
  · simp [gright, h3]

/-- Under the two Hopf conditions `a₁ = a₃Ω²`, `a₀ = (a₂ − Ω²)Ω²` the characteristic polynomial is
`(s² + Ω²)(s² + a₃ s + a₂ − Ω²)`. -/
@[tmio M, powerlib_domain] theorem Dg_factor {Ω : ℝ} (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (s : ℂ) :
    p.Dg s = (s ^ 2 + Ω ^ 2) * (s ^ 2 + p.da3 * s + (p.da2 - Ω ^ 2)) := by
  rw [p.Dg_eq]
  have hA' : (p.da1 : ℂ) = p.da3 * Ω ^ 2 := by exact_mod_cast hA
  have hB' : (p.da0 : ℂ) = (p.da2 - Ω ^ 2) * Ω ^ 2 := by exact_mod_cast hB
  linear_combination s * hA' + hB'

/-- The Hopf facts: `D(jΩ) = 0`, `D'(jΩ) = 2jΩ(a₂ − 2Ω² + j a₃Ω) ≠ 0`, `D(2jΩ) ≠ 0`. -/
@[tmio M, powerlib_domain] theorem ghopf_facts {Ω : ℝ} (hΩ : Ω ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) :
    p.Dg (Ω * I) = 0 ∧ p.Dgd (Ω * I) ≠ 0 ∧ p.Dg (((2 * Ω : ℝ) : ℂ) * I) ≠ 0 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  refine ⟨?_, ?_, ?_⟩
  · rw [p.Dg_factor hA hB]
    have : (Ω * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 := by linear_combination (Ω : ℂ) ^ 2 * Complex.I_sq
    rw [this, zero_mul]
  · intro h
    have hA' : (p.da1 : ℂ) = p.da3 * Ω ^ 2 := by exact_mod_cast hA
    have hre : (p.Dgd (Ω * I)).re = -2 * p.da3 * Ω ^ 2 := by
      simp only [Dgd]
      rw [hA']
      simp [pow_succ, Complex.mul_im, Complex.mul_re]
      ring
    rw [h, Complex.zero_re] at hre
    have : 0 < 2 * p.da3 * Ω ^ 2 := by positivity
    linarith
  · rw [p.Dg_factor hA hB]
    refine mul_ne_zero ?_ ?_
    · have : (((2 * Ω : ℝ) : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
        push_cast; linear_combination 4 * (Ω : ℂ) ^ 2 * Complex.I_sq
      rw [this]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hΩc)
    · intro h
      have him : ((((2 * Ω : ℝ) : ℂ) * I) ^ 2 + p.da3 * (((2 * Ω : ℝ) : ℂ) * I) +
          (p.da2 - Ω ^ 2)).im = 2 * Ω * p.da3 := by
        simp [pow_two, Complex.mul_im, Complex.mul_re]
        ring
      rw [h, Complex.zero_im] at him
      rcases mul_eq_zero.1 him.symm with h1 | h1
      · exact hΩ (by linarith)
      · linarith

/-- Under the Hopf conditions and `a₃ > 0`, `a₂ > Ω²`, every eigenvalue of `A₀` other than `±jΩ`
has negative real part. -/
@[tmio M, powerlib_domain] theorem geig_stable {Ω : ℝ} (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (μ : ℂ) (v : Fin 4 → ℂ) (hv : v ≠ 0) (he : p.A0.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (h1 : μ ≠ Ω * I) (h2 : μ ≠ -(Ω * I)) : μ.re < 0 := by
  have hP := p.geig_Dg hv he
  rw [p.Dg_factor hA hB] at hP
  rcases mul_eq_zero.1 hP with h | h
  · exfalso
    have h' : (μ - Ω * I) * (μ + Ω * I) = 0 := by
      linear_combination h - (Ω : ℂ) ^ 2 * Complex.I_sq
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact h1 (sub_eq_zero.1 h'')
    · exact h2 (eq_neg_of_add_eq_zero_left h'')
  · exact (Criteria.quadratic_roots_re_neg_iff _ _).2 ⟨h3, hq⟩ μ (by push_cast; exact h)

/-- `L_dc(jΩ) ≠ 0` follows from `D(jΩ) = 0` when the PLL–DVC coupling is present. -/
@[tmio M, powerlib_domain] theorem Ldc_ne_of_Dg {Ω : ℝ} (hG : p.Gam ≠ 0)
    (hki : p.ki ≠ 0) (hkiv : p.kiv ≠ 0) (hD : p.Dg (Ω * I) = 0) : p.Ldc (Ω * I) ≠ 0 := by
  intro hL
  simp only [Dg, hL, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hD
  rcases hD with (hD | hD) | hD
  · exact hG (by exact_mod_cast hD)
  · have := congrArg Complex.re hD
    simp at this
    exact hki this
  · have := congrArg Complex.re hD
    simp at this
    exact hkiv this


/-- The spectral data of `A₀` at a Hopf point, from explicit conditions: `r(jΩ)`, `l(jΩ)` are the
eigenvectors of `jΩ` with `l r = 1`, the eigenspace is spanned by `r(jΩ)`, and every other
eigenvalue has negative real part. -/
@[tmio M, powerlib_domain] theorem gspectral {Ω : ℝ} (hC : p.C ≠ 0) (hΩ : Ω ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2) :
    p.A0.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I) = ((Ω : ℂ) * I) • p.gright (Ω * I) ∧
      p.gleft (Ω * I) ᵥ* p.A0.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • p.gleft (Ω * I) ∧
      p.gleft (Ω * I) ⬝ᵥ p.gright (Ω * I) = 1 ∧
      (∀ v : Fin 4 → ℂ, p.A0.map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v →
        v = (p.gleft (Ω * I) ⬝ᵥ v) • p.gright (Ω * I)) ∧
      ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 → p.A0.map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
        μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0 := by
  have hs : (Ω : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hΩ) I_ne_zero
  have hk : (p.kp : ℂ) * (Ω * I) + p.ki ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hki this
  obtain ⟨hD, hd, -⟩ := p.ghopf_facts hΩ hA hB h3
  have hur := p.gleft_gright hC hs hk hL hD hd
  refine ⟨p.gright_eig hC hk hL hD, p.gleft_eig hC hs hL hD, hur, fun v hv => ?_,
    fun μ v hv he h1 h2 => p.geig_stable hA hB h3 hq μ v hv he h1 h2⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ, v = a • p.gright (Ω * I) := ⟨_, p.geig_span hC hk hL hv⟩
  subst ha
  rw [dotProduct_smul, hur, smul_eq_mul, mul_one]

/-- The GFL converter under the grid-angle variation `θ_g = θ_{g0} + ε cos 2Ωt`, end-to-end,
stability. At a Hopf point of `A₀` (`a₁ = a₃Ω²`, `a₀ = (a₂ − Ω²)Ω²`, `a₃ > 0`, `a₂ > Ω²`,
`L_dc(jΩ) ≠ 0`, `k_{i,PLL} ≠ 0`) with the damping and detuning `εA₀'`, `Re λ₁ < 0` and
`|g_m/2| < |λ₁|` (`λ₁ = l A₀' r`, `g_m = l A₁(z⁽¹⁾(2jΩ)) r̄`) give, for all small `ε > 0`, the
forced orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_hopf_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (p.gA1 (p.zc (((2 * Ω : ℝ) : ℂ) * I)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ p.afield (p.xs, 0) 1 (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  have hq0 : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hF0 : p.afield (p.xs, 0) = 0 := by
    have := p.field_xs hsd
    rw [p.field_eq_afield _ 0] at this
    simpa using this
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX p.afield (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matX_afield_xs hsd, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_afield hsd (ω := 2 * Ω) hD2
  have hA1 := p.smA1_afield hsd (p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable (p.contDiffAt_afield hq0) hF0
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under the grid-angle variation, end-to-end, parametric instability:
`|λ₁| < |g_m/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_hopf_unstable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (p.gA1 (p.zc (((2 * Ω : ℝ) : ℂ) * I)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ p.afield (p.xs, 0) 1 (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  have hq0 : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hF0 : p.afield (p.xs, 0) = 0 := by
    have := p.field_xs hsd
    rw [p.field_eq_afield _ 0] at this
    simpa using this
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX p.afield (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matX_afield_xs hsd, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_afield hsd (ω := 2 * Ω) hD2
  have hA1 := p.smA1_afield hsd (p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable (p.contDiffAt_afield hq0)
    hF0 (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_
  rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under the grid-angle variation, end-to-end: the forced orbit exists and is
locally exponentially stable for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_hopf_exp_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (p.gA1 (p.zc (((2 * Ω : ℝ) : ℂ) * I)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
        ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t v => p.afield ((p.xs, 0).1 + v, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  have hq0 : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hF0 : p.afield (p.xs, 0) = 0 := by
    have := p.field_xs hsd
    rw [p.field_eq_afield _ 0] at this
    simpa using this
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX p.afield (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matX_afield_xs hsd, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_afield hsd (ω := 2 * Ω) hD2
  have hA1 := p.smA1_afield hsd (p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable (p.contDiffAt_afield hq0) hF0
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

end Params
end powerlib.GFL.Parametric.AngleModulation
