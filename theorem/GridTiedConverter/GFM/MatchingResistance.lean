import theorem.GridTiedConverter.GFM.MatchingNetwork
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-! # Matching control: the network-resistance term of (14)

The first-order coefficient of the link resistance `R` in the matching damping formula (14) is
the derivative `∂σ/∂R` of the decay rate `σ = −Re λ` at the base point where the other first-order
terms vanish (`1/τ = 1/ω_f = G = R = 0`). At that point the six-state core of `MatchingNetwork`
reduces to the spring-swing characteristic function
`F(s, R) = C s² + k_s + s K_v(s, R) + ω_b K_θ(s, R)` (`spring_limit`), whose lossless mode is
exactly `jΩ`, `C Ω² = k_s + ω_b K` (`Fss_zero`). The implicit function theorem gives a
differentiable mode `λ(R)` (`exists_root_branch₂`, `exists_branch`); its slope is derived in
closed form (`resistance_slope`), and the normalized coefficient is `report14_resistance`.

Model boundary.
* The core of `MatchingNetwork.Model` (constant `m_a`, `V`, `X`, dynamic series link `R + jX` in
  the frame of the nominal grid frequency) with the DC source `k_dc = k_s τ`, `G = 0`, in the limit
  `τ, ω_f → ∞` (`spring`, `spring_limit`); `K_v`, `K_θ` of a general link (`Kv_eq`, `Hj_eq`,
  `Pθ_eq`, `Kv_withR`, `Kθ_withR`, `Fss_eq`).
* The equilibrium angle may move with `R` along any differentiable `δ₀(R)` (`branch_deriv`,
  `resistance_slope`); this changes only the frequency.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §4 (matching, (14): `(1 + κ_dc) σ_m/Ω_m ≈ κ_dc/(2Ω_m τ) − Ω_m/(2ω_f)
− (R/X) μ/(2 cos δ₀) + (1 + κ_dc) G_dc/(2CΩ_m) + ⋯`, the term "网络电阻"), §3 (matching core,
`κ_dc = k_dc/(τ ω_b K)`, `Ω_m² ≈ ω_b K (1 + κ_dc)/C`), and `verification/check_matching.py`.

Results.
* `exists_root_branch₂` — implicit function theorem for a root of `f(R, s)` with continuous
  partial derivatives and `∂_s f ≠ 0`.
* `spring_limit` — `D(s) → F(s, R)/ω_b` for `τ, ω_f → ∞`, `k_dc = k_s τ`, `G = 0`.
* `Fss_zero` (`F(s, 0) = C s² + k_s + ω_b K`), `FsR_zero` (`F_s(s, 0) = 2Cs`), `FRR_zero`
  (`F_R(s, 0) = ω_b m_a V sin δ₀/X² − (m_a²/X²) ω_b² s/(s² + ω_b²)`), `Fδ_zero`
  (`F_δ(0) = −ω_b m_a V sin δ₀/X`, real).
* `branch_deriv` — `F_s λ' + F_R + F_δ δ₀' = 0` along every differentiable root branch.
* `resistance_slope` — `λ'(0) = (m_a²/X²) ω_b²/(2C(ω_b² − Ω²)) + j ω_b m_a V sin δ₀ (1/X − δ₀')/(2CΩX)`.
* `report14_resistance`, `report14_resistance_branch` — with `μ = Ω/ω_b`, `κ_dc = k_s/(ω_b K)`:
  `(1 + κ_dc) σ'(0)/Ω = −(1/X)(m_a/V) μ/(2 cos δ₀) · 1/(1 − μ²)`, exactly.

Corrections.
* The network-resistance term of (14) is `−(R/X) (E/V) μ/(2 cos δ₀) · 1/(1 − μ²)`, `E = m_a v₀`:
  the source's `−(R/X) μ/(2 cos δ₀)` is its leading order in `μ` for `E = V` only. The factor
  `E/V` is `O(1)`, not small; `1/(1 − μ²)` is the sideband correction (`1.0025`, `1.010`,
  `1.067` at `μ = 0.05, 0.1, 0.25`).

Family and connection conclusions.
None: static evidence on the matching core (characteristic function, implicit root branch).
-/

noncomputable section

namespace powerlib.GFM
namespace MatchingNetwork
open Complex Filter Topology

/-- Root branches of a function of a complex frequency and a real parameter (implicit
function theorem): continuous partial derivatives near `(R₀, s₀)` and a simple root give a
differentiable root branch `λ(R)` through `λ(R₀) = s₀`. -/
@[tmio T, powerlib_foundation] theorem exists_root_branch₂ {f fR fs : ℝ → ℂ → ℂ} {R0 : ℝ} {s0 : ℂ}
    (hR : ∀ᶠ v in 𝓝 (R0, s0), HasDerivAt (fun R => f R v.2) (fR v.1 v.2) v.1)
    (hs : ∀ᶠ v in 𝓝 (R0, s0), HasDerivAt (fun s => f v.1 s) (fs v.1 v.2) v.2)
    (cR : ContinuousAt (fun v : ℝ × ℂ => fR v.1 v.2) (R0, s0))
    (cs : ContinuousAt (fun v : ℝ × ℂ => fs v.1 v.2) (R0, s0))
    (hne : fs R0 s0 ≠ 0) (h0 : f R0 s0 = 0) :
    ∃ lam : ℝ → ℂ, lam R0 = s0 ∧ (∀ᶠ R in 𝓝 R0, f R (lam R) = 0) ∧ DifferentiableAt ℝ lam R0 := by
  let L1 : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℂ)
  let f₁ : ℝ → ℂ → ℝ →L[ℝ] ℂ := fun R s => fR R s • L1
  let f₂ : ℝ → ℂ → ℂ →L[ℝ] ℂ := fun R s => fs R s • ContinuousLinearMap.id ℝ ℂ
  have df₁ : ∀ᶠ v in 𝓝 (R0, s0), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1 := by
    filter_upwards [hR] with v hv
    convert hv.hasFDerivAt using 1
    ext
    simp [f₁, L1]
  have df₂ : ∀ᶠ v in 𝓝 (R0, s0), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2 := by
    filter_upwards [hs] with v hv
    convert hv.hasFDerivAt.restrictScalars ℝ using 1
    ext z
    simp [f₂, mul_comm]
  have cf₁ : ContinuousAt ↿f₁ (R0, s0) := cR.smul continuousAt_const
  have cf₂ : ContinuousAt ↿f₂ (R0, s0) := cs.smul continuousAt_const
  have hinv : (f₂ (R0, s0).1 (R0, s0).2).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.equivOfInverse (f₂ R0 s0)
      ((fs R0 s0)⁻¹ • ContinuousLinearMap.id ℝ ℂ) (fun z => ?_) (fun z => ?_), rfl⟩
    · simp [f₂, ← mul_assoc, inv_mul_cancel₀ hne]
    · simp [f₂, ← mul_assoc, mul_inv_cancel₀ hne]
  refine ⟨implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv, ?_, ?_, ?_⟩
  · exact ((eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv).self_of_nhds).mp rfl
  · filter_upwards [eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv] with R hR
    rw [hR]; exact h0
  · exact (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv).differentiableAt

namespace Model

variable (p : Model)

/-! ### The DC-row transfers of a general link -/

@[tmio M, powerlib_domain] theorem Kv_eq (δ0 : ℝ) (s : ℂ) :
    (p.coeffs δ0).Kv s = p.an * p.ma ^ 2 / 2 * (1 / (s + p.an * p.Z) + 1 / (s + p.an * p.Zc)) := by
  have hV := p.φ_mul_φt δ0
  simp only [Coeffs.Kv, Coeffs.h, Coeffs.ht, coeffs, idci, idcm]
  linear_combination ((p.an : ℂ) / 2 * (1 / (s + p.an * p.Z) + 1 / (s + p.an * p.Zc))) * hV

@[tmio M, powerlib_domain] theorem Hj_eq (δ0 : ℝ) (s : ℂ) :
    (p.coeffs δ0).Hj s =
      I * (p.an * p.ma ^ 2 / 2) * (1 / (s + p.an * p.Z) - 1 / (s + p.an * p.Zc)) := by
  have hV := p.φ_mul_φt δ0
  simp only [Coeffs.Hj, Coeffs.h, Coeffs.ht, coeffs, idci, idcm]
  linear_combination (I * (p.an : ℂ) / 2 * (1 / (s + p.an * p.Z) - 1 / (s + p.an * p.Zc))) * hV

@[tmio M, powerlib_domain] theorem Pθ_eq (δ0 : ℝ) :
    (p.coeffs δ0).Pθ = (I * (p.ma ^ 2 - p.V * p.φ δ0) / p.Zc - I * (p.ma ^ 2 - p.V * p.φt δ0) / p.Z) / 2 := by
  have hV := p.φ_mul_φt δ0
  simp only [coeffs, idcθ, i0, m0]
  linear_combination (I / (2 * p.Zc) - I / (2 * p.Z)) * hV

/-! ### The link resistance as a parameter -/

/-- The model with link resistance `R`. -/
def withR (R : ℝ) : Model := { p with R := R }

/-- `K_v` of the link `R + jX`. -/
def KvR (s : ℂ) (R : ℝ) : ℂ :=
  p.an * p.ma ^ 2 / 2 * (1 / (s + p.an * (R + p.X * I)) + 1 / (s + p.an * (R - p.X * I)))
/-- `H_j` of the link `R + jX`. -/
def HjR (s : ℂ) (R : ℝ) : ℂ :=
  I * (p.an * p.ma ^ 2 / 2) * (1 / (s + p.an * (R + p.X * I)) - 1 / (s + p.an * (R - p.X * I)))
/-- The Park element of the link `R + jX` at the angle `δ₀`. -/
def PθR (δ0 : ℝ) (R : ℝ) : ℂ :=
  (I * (p.ma ^ 2 - p.V * p.φ δ0) / (R - p.X * I) - I * (p.ma ^ 2 - p.V * p.φt δ0) / (R + p.X * I)) / 2

@[tmio M, powerlib_domain] theorem Kv_withR (δ0 R : ℝ) (s : ℂ) :
    ((p.withR R).coeffs δ0).Kv s = p.KvR s R :=
  (p.withR R).Kv_eq δ0 s

@[tmio M, powerlib_domain] theorem Kθ_withR (δ0 R : ℝ) (s : ℂ) :
    ((p.withR R).coeffs δ0).Kθ s = p.PθR δ0 R + p.HjR s R := by
  rw [Coeffs.Kθ, (p.withR R).Pθ_eq δ0, (p.withR R).Hj_eq δ0 s]
  rfl

/-- The characteristic function of the spring-swing limit (`G = 0`, `k_dc = k_s τ`, `τ → ∞`,
`ω_f → ∞`; `spring_limit`), with link resistance `R`:
`F(s, R) = C s² + k_s + s K_v(s) + ω_b K_θ(s)`. -/
def Fss (ks δ0 : ℝ) (s : ℂ) (R : ℝ) : ℂ :=
  p.C * s ^ 2 + ks + s * ((p.withR R).coeffs δ0).Kv s + p.ωb * ((p.withR R).coeffs δ0).Kθ s

@[tmio M, powerlib_domain] theorem Fss_eq (ks δ0 : ℝ) (s : ℂ) (R : ℝ) :
    p.Fss ks δ0 s R = p.C * s ^ 2 + ks + s * p.KvR s R + p.ωb * (p.PθR δ0 R + p.HjR s R) := by
  rw [Fss, Kv_withR, Kθ_withR]

/-- The model with link resistance `R`, no DC load, the DC source `k_dc = k_s τ` and the
measurement filter `ω_f`. -/
def spring (ks τ ωf R : ℝ) : Model := { p with R := R, G := 0, τ := τ, kdc := ks * τ, ωf := ωf }

/-- The spring-swing limit: for `τ, ω_f → ∞` with `k_dc = k_s τ` and `G = 0`, the characteristic
function `D(s)` of the full core tends to `F(s, R)/ω_b`. -/
@[tmio M, powerlib_domain] theorem spring_limit (ks δ0 R : ℝ) (s : ℂ) (hs : s ≠ 0) (hωb : p.ωb ≠ 0) :
    Tendsto (fun x : ℝ × ℝ => ((p.spring ks x.1 x.2 R).coeffs δ0).D s) (atTop ×ˢ atTop)
      (𝓝 (p.Fss ks δ0 s R / p.ωb)) := by
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have ha : Tendsto (fun x : ℝ × ℝ => ((x.1⁻¹ : ℝ) : ℂ)) (atTop ×ˢ atTop) (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ × ℝ => x.1) (atTop ×ˢ atTop) atTop := tendsto_fst
    have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp h0)
    rw [ofReal_zero] at h
    exact h
  have hb : Tendsto (fun x : ℝ × ℝ => ((x.2⁻¹ : ℝ) : ℂ)) (atTop ×ˢ atTop) (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ × ℝ => x.2) (atTop ×ˢ atTop) atTop := tendsto_snd
    have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp h0)
    rw [ofReal_zero] at h
    exact h
  have hev : ∀ᶠ x : ℝ × ℝ in atTop ×ˢ atTop,
      ((p.spring ks x.1 x.2 R).coeffs δ0).D s =
        (p.C * s + ks / (s + ((x.1⁻¹ : ℝ) : ℂ)) + p.KvR s R) * (s * (1 + s * ((x.2⁻¹ : ℝ) : ℂ)) / p.ωb) +
          (p.PθR δ0 R + p.HjR s R) := by
    have h1 : ∀ᶠ x : ℝ × ℝ in atTop ×ˢ atTop, 0 < x.1 :=
      (tendsto_fst : Tendsto (fun x : ℝ × ℝ => x.1) (atTop ×ˢ atTop) atTop).eventually
        (eventually_gt_atTop 0)
    have h2 : ∀ᶠ x : ℝ × ℝ in atTop ×ˢ atTop, 0 < x.2 :=
      (tendsto_snd : Tendsto (fun x : ℝ × ℝ => x.2) (atTop ×ˢ atTop) atTop).eventually
        (eventually_gt_atTop 0)
    filter_upwards [h1, h2] with x hx1 hx2
    have hKv : ((p.spring ks x.1 x.2 R).coeffs δ0).Kv s = p.KvR s R :=
      (p.spring ks x.1 x.2 R).Kv_eq δ0 s
    have hKθ : ((p.spring ks x.1 x.2 R).coeffs δ0).Kθ s = p.PθR δ0 R + p.HjR s R := by
      rw [Coeffs.Kθ, (p.spring ks x.1 x.2 R).Pθ_eq δ0, (p.spring ks x.1 x.2 R).Hj_eq δ0 s]
      rfl
    rw [Coeffs.D, Coeffs.M, hKv, hKθ]
    have hτ : (x.1 : ℂ) ≠ 0 := by exact_mod_cast hx1.ne'
    have hf : (x.2 : ℂ) ≠ 0 := by exact_mod_cast hx2.ne'
    have e1 : ((p.spring ks x.1 x.2 R).coeffs δ0).kdc / (((p.spring ks x.1 x.2 R).coeffs δ0).τ * s + 1) =
        ks / (s + ((x.1⁻¹ : ℝ) : ℂ)) := by
      simp only [coeffs, spring]
      push_cast
      rw [show (x.1 : ℂ) * s + 1 = x.1 * (s + (x.1 : ℂ)⁻¹) by field_simp, mul_comm (ks : ℂ),
        mul_div_mul_left _ _ hτ]
    have e2 : ((p.spring ks x.1 x.2 R).coeffs δ0).ρv s = s * (1 + s * ((x.2⁻¹ : ℝ) : ℂ)) / p.ωb := by
      simp only [Coeffs.ρv, coeffs, spring]
      push_cast
      field_simp
      ring
    rw [e1, e2]
    simp only [coeffs, spring]
    push_cast
    ring
  have hs0 : s + (0 : ℂ) ≠ 0 := by simpa using hs
  have hlim := ((((tendsto_const_nhds (x := (p.C : ℂ) * s)).add
    ((tendsto_const_nhds (x := (ks : ℂ))).div ((tendsto_const_nhds (x := s)).add ha) hs0)).add
      (tendsto_const_nhds (x := p.KvR s R))).mul
    (((tendsto_const_nhds (x := s)).mul ((tendsto_const_nhds (x := (1 : ℂ))).add
      ((tendsto_const_nhds (x := s)).mul hb))).div_const (p.ωb : ℂ))).add
    (tendsto_const_nhds (x := p.PθR δ0 R + p.HjR s R))
  have hval : ((p.C : ℂ) * s + ks / (s + 0) + p.KvR s R) * (s * (1 + s * 0) / p.ωb) +
      (p.PθR δ0 R + p.HjR s R) = p.Fss ks δ0 s R / p.ωb := by
    rw [Fss_eq]
    field_simp
    ring
  rw [← hval]
  exact hlim.congr' (hev.mono fun x hx => hx.symm)

/-! ### The base mode and the partial derivatives -/

@[tmio M, powerlib_domain] theorem an_link_zero (hX : p.X ≠ 0) :
    (p.an : ℂ) * (((0 : ℝ) : ℂ) + p.X * I) = p.ωb * I ∧
      (p.an : ℂ) * (((0 : ℝ) : ℂ) - p.X * I) = -(p.ωb * I) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  simp only [an]
  push_cast
  constructor <;> (field_simp; ring)

@[tmio M, powerlib_domain] theorem φ_expand (δ0 : ℝ) :
    p.φ δ0 = p.ma * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) ∧
      p.φt δ0 = p.ma * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
  constructor
  · simp only [φ]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  · simp only [φt]; rw [PSCActiveDamping.exp_neg_mul_I]

/-- The base mode: with a lossless link the spring-swing characteristic function is the
undamped oscillator `F(s, 0) = C s² + k_s + ω_b K`, `K = m_a V cos δ₀/X`. -/
@[tmio M, powerlib_domain] theorem Fss_zero (ks δ0 : ℝ) (s : ℂ) (hX : p.X ≠ 0)
    (h1 : s + p.ωb * I ≠ 0) (h2 : s - p.ωb * I ≠ 0) :
    p.Fss ks δ0 s 0 = p.C * s ^ 2 + ks + p.ωb * ((p.ma * p.V * Real.cos δ0 / p.X : ℝ) : ℂ) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  obtain ⟨e1, e2⟩ := p.an_link_zero hX
  obtain ⟨f1, f2⟩ := p.φ_expand δ0
  rw [Fss_eq]
  simp only [KvR, HjR, PθR, e1, e2, f1, f2]
  rw [show s + -((p.ωb : ℂ) * I) = s - p.ωb * I by ring]
  have hsum : (s + p.ωb * I) + (s - p.ωb * I) = 2 * s := by ring
  have hdiff : (s + p.ωb * I) - (s - p.ωb * I) = 2 * (p.ωb * I) := by ring
  have hz1 : ((0 : ℝ) : ℂ) - p.X * I = -(p.X * I) := by simp
  have hz2 : ((0 : ℝ) : ℂ) + p.X * I = p.X * I := by simp
  have hprod : (s + p.ωb * I) * (s - p.ωb * I) = s ^ 2 + (p.ωb : ℂ) ^ 2 := by
    ring_nf; rw [I_sq]; ring
  rw [hz1, hz2]
  generalize s + p.ωb * I = u1 at h1 hsum hdiff hprod ⊢
  generalize s - p.ωb * I = u2 at h2 hsum hdiff hprod ⊢
  simp only [an]
  push_cast
  field_simp
  linear_combination (s * p.ωb * (p.ma : ℂ) ^ 2) * hsum + (-((p.ωb : ℂ) ^ 2 * (p.ma : ℂ) ^ 2 * I)) * hdiff +
    (-2 * p.ωb * (p.ma : ℂ) ^ 2) * hprod + (-2 * (p.ωb : ℂ) ^ 3 * (p.ma : ℂ) ^ 2) * I_sq

/-- `∂F/∂s`. -/
def FsR (s : ℂ) (R : ℝ) : ℂ :=
  2 * p.C * s + p.KvR s R -
    s * (p.an * p.ma ^ 2 / 2 * (1 / (s + p.an * (R + p.X * I)) ^ 2 + 1 / (s + p.an * (R - p.X * I)) ^ 2)) -
    p.ωb * (I * (p.an * p.ma ^ 2 / 2) *
      (1 / (s + p.an * (R + p.X * I)) ^ 2 - 1 / (s + p.an * (R - p.X * I)) ^ 2))
/-- `∂F/∂R` at a fixed angle. -/
def FRR (δ0 : ℝ) (s : ℂ) (R : ℝ) : ℂ :=
  -(p.an * (s * (p.an * p.ma ^ 2 / 2 *
      (1 / (s + p.an * (R + p.X * I)) ^ 2 + 1 / (s + p.an * (R - p.X * I)) ^ 2)) +
    p.ωb * (I * (p.an * p.ma ^ 2 / 2) *
      (1 / (s + p.an * (R + p.X * I)) ^ 2 - 1 / (s + p.an * (R - p.X * I)) ^ 2)))) +
  p.ωb * (-(I * (p.ma ^ 2 - p.V * p.φ δ0)) / (R - p.X * I) ^ 2 +
    I * (p.ma ^ 2 - p.V * p.φt δ0) / (R + p.X * I) ^ 2) / 2
/-- `∂F/∂δ₀`. -/
def Fδ (δ0 : ℝ) (R : ℝ) : ℂ :=
  p.ωb * (p.V * p.φ δ0 / (R - p.X * I) + p.V * p.φt δ0 / (R + p.X * I)) / 2

/-- Implicit differentiation along a root branch: if the mode `λ(R)` and the equilibrium angle
`δ₀(R)` are differentiable at `R = 0` and `F(λ(R), R) = 0` near `R = 0`, then
`F_s λ'(0) + F_R + F_δ δ₀'(0) = 0`. -/
@[tmio M, powerlib_domain] theorem branch_deriv (ks : ℝ) {δ : ℝ → ℝ} {d : ℝ} {lam : ℝ → ℂ} {l' : ℂ}
    (hX : p.X ≠ 0) (hδ : HasDerivAt δ d 0) (hl : HasDerivAt lam l' 0)
    (h1 : lam 0 + p.an * (((0 : ℝ) : ℂ) + p.X * I) ≠ 0)
    (h2 : lam 0 + p.an * (((0 : ℝ) : ℂ) - p.X * I) ≠ 0)
    (hroot : ∀ᶠ R in 𝓝 (0 : ℝ), p.Fss ks (δ R) (lam R) R = 0) :
    p.FsR (lam 0) 0 * l' + p.FRR (δ 0) (lam 0) 0 + p.Fδ (δ 0) 0 * d = 0 := by
  have hz1 : ((0 : ℝ) : ℂ) - p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hz2 : ((0 : ℝ) : ℂ) + p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hR : HasDerivAt (fun R : ℝ => (R : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hu1 : HasDerivAt (fun R : ℝ => lam R + p.an * ((R : ℂ) + p.X * I)) (l' + p.an * 1) 0 :=
    hl.add ((hR.add_const _).const_mul _)
  have hu2 : HasDerivAt (fun R : ℝ => lam R + p.an * ((R : ℂ) - p.X * I)) (l' + p.an * 1) 0 :=
    hl.add ((hR.sub_const _).const_mul _)
  have hi1 := hu1.inv h1
  have hi2 := hu2.inv h2
  have hj1 := (hR.sub_const (p.X * I : ℂ)).inv hz1
  have hj2 := (hR.add_const (p.X * I : ℂ)).inv hz2
  have hδc : HasDerivAt (fun R : ℝ => ((δ R : ℝ) : ℂ)) d 0 := hδ.ofReal_comp
  have hφ := HasDerivAt.comp (h := fun R : ℝ => ((δ R : ℝ) : ℂ)) (0 : ℝ)
    (p.hasDerivAt_φ ((δ 0 : ℝ) : ℂ)) hδc
  have hφt := HasDerivAt.comp (h := fun R : ℝ => ((δ R : ℝ) : ℂ)) (0 : ℝ)
    (p.hasDerivAt_φt ((δ 0 : ℝ) : ℂ)) hδc
  have hKv := (hi1.add hi2).const_mul ((p.an : ℂ) * p.ma ^ 2 / 2)
  have hHj := (hi1.sub hi2).const_mul (I * ((p.an : ℂ) * p.ma ^ 2 / 2))
  have hP1 := ((hφ.const_mul (-(p.V : ℂ))).const_add ((p.ma : ℂ) ^ 2)).const_mul I
  have hP2 := ((hφt.const_mul (-(p.V : ℂ))).const_add ((p.ma : ℂ) ^ 2)).const_mul I
  have hP := ((hP1.mul hj1).sub (hP2.mul hj2)).div_const 2
  have h := ((((hl.mul hl).const_mul (p.C : ℂ)).add_const (ks : ℂ)).add (hl.mul hKv)).add
    ((hP.add hHj).const_mul (p.ωb : ℂ))
  have hG : HasDerivAt (fun R : ℝ => p.Fss ks (δ R) (lam R) R)
      (p.FsR (lam 0) 0 * l' + p.FRR (δ 0) (lam 0) 0 + p.Fδ (δ 0) 0 * d) 0 := by
    convert h using 1
    · funext R
      simp only [Fss_eq, KvR, HjR, PθR, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, Pi.mul_apply,
        Function.comp_apply]
      ring
    · simp only [FsR, FRR, Fδ, KvR, Function.comp_apply, Pi.add_apply, Pi.inv_apply]
      linear_combination ((p.ωb : ℂ) * d * p.V / 2 * (p.φ (δ 0) / (((0 : ℝ) : ℂ) - p.X * I) +
        p.φt (δ 0) / (((0 : ℝ) : ℂ) + p.X * I))) * I_sq
  have hzero : HasDerivAt (fun R : ℝ => p.Fss ks (δ R) (lam R) R) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hroot
  exact hG.unique hzero

/-- `F_s(s, 0) = 2 C s`: with a lossless link `s K_v(s) + ω_b H_j(s) = (m_a²/X) ω_b` is constant. -/
@[tmio M, powerlib_domain] theorem FsR_zero (s : ℂ) (hX : p.X ≠ 0)
    (h1 : s + p.ωb * I ≠ 0) (h2 : s - p.ωb * I ≠ 0) : p.FsR s 0 = 2 * p.C * s := by
  obtain ⟨e1, e2⟩ := p.an_link_zero hX
  simp only [FsR, KvR, e1, e2]
  rw [show s + -((p.ωb : ℂ) * I) = s - p.ωb * I by ring]
  have hsum : (s + p.ωb * I) + (s - p.ωb * I) = 2 * s := by ring
  have hdiff : (s + p.ωb * I) - (s - p.ωb * I) = 2 * (p.ωb * I) := by ring
  generalize s + p.ωb * I = u1 at h1 hsum hdiff ⊢
  generalize s - p.ωb * I = u2 at h2 hsum hdiff ⊢
  field_simp
  linear_combination ((p.an : ℂ) * p.ma ^ 2 * (u1 ^ 2 + u2 ^ 2) / 2) * hsum +
    ((p.an : ℂ) * p.ma ^ 2 * (u2 ^ 2 - u1 ^ 2) / 2) * hdiff

/-- `F_R(s, 0) = ω_b m_a V sin δ₀/X² − (m_a²/X²) ω_b² s/(s² + ω_b²)`. -/
@[tmio M, powerlib_domain] theorem FRR_zero (δ0 : ℝ) (s : ℂ) (hX : p.X ≠ 0)
    (h1 : s + p.ωb * I ≠ 0) (h2 : s - p.ωb * I ≠ 0) :
    p.FRR δ0 s 0 = p.ωb * ((p.ma * p.V * Real.sin δ0 / p.X ^ 2 : ℝ) : ℂ) -
      ((p.ma ^ 2 / p.X ^ 2 : ℝ) : ℂ) * p.ωb ^ 2 * s / (s ^ 2 + (p.ωb : ℂ) ^ 2) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  obtain ⟨e1, e2⟩ := p.an_link_zero hX
  obtain ⟨f1, f2⟩ := p.φ_expand δ0
  simp only [FRR, e1, e2, f1, f2]
  rw [show s + -((p.ωb : ℂ) * I) = s - p.ωb * I by ring]
  have hsum : (s + p.ωb * I) + (s - p.ωb * I) = 2 * s := by ring
  have hdiff : (s + p.ωb * I) - (s - p.ωb * I) = 2 * (p.ωb * I) := by ring
  have hprod : (s + p.ωb * I) * (s - p.ωb * I) = s ^ 2 + (p.ωb : ℂ) ^ 2 := by
    ring_nf; rw [I_sq]; ring
  have hz1 : ((0 : ℝ) : ℂ) - p.X * I = -(p.X * I) := by simp
  have hz2 : ((0 : ℝ) : ℂ) + p.X * I = p.X * I := by simp
  rw [hz1, hz2, ← hprod]
  generalize s + p.ωb * I = u1 at h1 hsum hdiff ⊢
  generalize s - p.ωb * I = u2 at h2 hsum hdiff ⊢
  simp only [an]
  push_cast
  field_simp
  linear_combination ((p.ωb : ℂ) ^ 2 * p.ma ^ 2 * I * (u1 - u2) ^ 2 / 2) * hsum +
    ((p.ωb : ℂ) ^ 2 * p.ma ^ 2 * I * (u2 ^ 2 - u1 ^ 2) / 2) * hdiff

/-- `F_δ(0) = −ω_b m_a V sin δ₀/X`: real. -/
@[tmio M, powerlib_domain] theorem Fδ_zero (δ0 : ℝ) (hX : p.X ≠ 0) :
    p.Fδ δ0 0 = -(p.ωb * ((p.ma * p.V * Real.sin δ0 / p.X : ℝ) : ℂ)) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  obtain ⟨f1, f2⟩ := p.φ_expand δ0
  simp only [Fδ, f1, f2]
  have hz1 : ((0 : ℝ) : ℂ) - p.X * I = -(p.X * I) := by simp
  have hz2 : ((0 : ℝ) : ℂ) + p.X * I = p.X * I := by simp
  rw [hz1, hz2]
  push_cast
  field_simp
  ring

/-! ### The resistance slope of the mode -/

@[tmio M, powerlib_domain] theorem hopf_ne (Ω : ℝ) (hμ : Ω ^ 2 ≠ p.ωb ^ 2) :
    (Ω : ℂ) * I + p.ωb * I ≠ 0 ∧ (Ω : ℂ) * I - p.ωb * I ≠ 0 := by
  constructor
  · intro h
    have h' : ((Ω + p.ωb : ℝ) : ℂ) * I = 0 := by push_cast; linear_combination h
    have : Ω + p.ωb = 0 := by exact_mod_cast (by simpa using h' : (Ω : ℂ) + p.ωb = 0)
    apply hμ; have : Ω = -p.ωb := by linarith
    rw [this]; ring
  · intro h
    have h' : ((Ω - p.ωb : ℝ) : ℂ) * I = 0 := by push_cast; linear_combination h
    have : Ω - p.ωb = 0 := by exact_mod_cast (by simpa using h' : (Ω : ℂ) - p.ωb = 0)
    apply hμ; have : Ω = p.ωb := by linarith
    rw [this]

/-- The resistance slope of the mode. Along every differentiable root branch `λ(R)` of the
spring-swing characteristic function through the lossless mode `λ(0) = jΩ`, with any
differentiable equilibrium angle `δ₀(R)`:
`λ'(0) = (m_a²/X²) ω_b²/(2C(ω_b² − Ω²)) + j ω_b m_a V sin δ₀ (1/X − δ₀'(0))/(2CΩX)`.
The angle shift only moves the frequency. -/
@[tmio M, powerlib_domain] theorem resistance_slope (ks Ω : ℝ) {δ : ℝ → ℝ} {d : ℝ} {lam : ℝ → ℂ}
    {l' : ℂ} (hX : p.X ≠ 0) (hC : p.C ≠ 0) (hΩ : Ω ≠ 0) (hμ : Ω ^ 2 ≠ p.ωb ^ 2)
    (hδ : HasDerivAt δ d 0) (hl : HasDerivAt lam l' 0) (h0 : lam 0 = Ω * I)
    (hroot : ∀ᶠ R in 𝓝 (0 : ℝ), p.Fss ks (δ R) (lam R) R = 0) :
    l' = ((p.ma ^ 2 * p.ωb ^ 2 / (2 * p.C * p.X ^ 2 * (p.ωb ^ 2 - Ω ^ 2)) : ℝ) : ℂ) +
      I * ((p.ωb * p.ma * p.V * Real.sin (δ 0) / (2 * p.C * Ω * p.X) * (1 / p.X - d) : ℝ) : ℂ) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hμc : (p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2 ≠ 0 := by
    intro h; apply hμ; have : ((p.ωb ^ 2 - Ω ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have := (ofReal_eq_zero.mp this); linarith
  obtain ⟨h1, h2⟩ := p.hopf_ne Ω hμ
  obtain ⟨e1, e2⟩ := p.an_link_zero hX
  have hb := p.branch_deriv ks hX hδ hl (by rw [h0, e1]; exact h1)
    (by rw [h0, e2, show (Ω : ℂ) * I + -(p.ωb * I) = Ω * I - p.ωb * I by ring]; exact h2) hroot
  rw [h0, p.FsR_zero _ hX h1 h2, p.FRR_zero _ _ hX h1 h2, p.Fδ_zero _ hX] at hb
  rw [show ((Ω : ℂ) * I) ^ 2 + (p.ωb : ℂ) ^ 2 = (p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2 by
    ring_nf; rw [I_sq]; ring] at hb
  have hFs : 2 * (p.C : ℂ) * (Ω * I) ≠ 0 := by
    simp [hCc, hΩc, I_ne_zero]
  apply mul_left_cancel₀ hFs
  push_cast at hb ⊢
  field_simp at hb ⊢
  linear_combination (-I) * hb + (2 * p.C * Ω * l' * p.X ^ 2 * ((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) -
    (p.ωb : ℂ) ^ 2 * p.ma ^ 2 * Ω) * I_sq

/-- The network-resistance term of (14), exactly. With `K = m_a V cos δ₀/X`,
`κ_dc = k_s/(ω_b K)` and `μ = Ω/ω_b`, the decay rate `σ = −Re λ` of the mode has the slope
`(1 + κ_dc) σ'(0)/Ω = −(1/X) (m_a/V) μ/(2 cos δ₀) · 1/(1 − μ²)`:
the source's `−(R/X) μ/(2 cos δ₀)` times `(E/V)/(1 − μ²)`, `E = m_a v₀ = m_a`. -/
@[tmio M, powerlib_domain] theorem report14_resistance (ks Ω : ℝ) {δ : ℝ → ℝ} {d : ℝ}
    {lam : ℝ → ℂ} {l' : ℂ} (hX : p.X ≠ 0) (hC : p.C ≠ 0) (hΩ : Ω ≠ 0) (hμ : Ω ^ 2 ≠ p.ωb ^ 2)
    (hωb : p.ωb ≠ 0) (hma : p.ma ≠ 0) (hV : p.V ≠ 0) (hc : Real.cos (δ 0) ≠ 0)
    (hδ : HasDerivAt δ d 0) (hl : HasDerivAt lam l' 0) (h0 : lam 0 = Ω * I)
    (hroot : ∀ᶠ R in 𝓝 (0 : ℝ), p.Fss ks (δ R) (lam R) R = 0) :
    (1 + ks / (p.ωb * (p.ma * p.V * Real.cos (δ 0) / p.X))) * (-l'.re) / Ω =
      -(1 / p.X) * (p.ma / p.V) * ((Ω / p.ωb) / (2 * Real.cos (δ 0))) / (1 - (Ω / p.ωb) ^ 2) := by
  obtain ⟨h1, h2⟩ := p.hopf_ne Ω hμ
  have h00 := hroot.self_of_nhds
  rw [h0, p.Fss_zero _ _ _ hX h1 h2,
    show ((Ω : ℂ) * I) ^ 2 = ((-Ω ^ 2 : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring] at h00
  have hk : p.C * (-Ω ^ 2) + ks + p.ωb * (p.ma * p.V * Real.cos (δ 0) / p.X) = 0 := by
    exact_mod_cast h00
  have hre : l'.re = p.ma ^ 2 * p.ωb ^ 2 / (2 * p.C * p.X ^ 2 * (p.ωb ^ 2 - Ω ^ 2)) := by
    rw [p.resistance_slope ks Ω hX hC hΩ hμ hδ hl h0 hroot]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    ring
  have hks : ks = p.C * Ω ^ 2 - p.ωb * (p.ma * p.V * Real.cos (δ 0) / p.X) := by linarith
  have hQ : p.ωb ^ 2 - Ω ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  have hQ' : 1 - (Ω / p.ωb) ^ 2 ≠ 0 := by
    rw [div_pow, one_sub_div (pow_ne_zero 2 hωb)]
    exact div_ne_zero hQ (pow_ne_zero 2 hωb)
  rw [hre, hks]
  field_simp
  ring

/-! ### Existence of the root branch -/

@[tmio M, powerlib_domain] theorem hasDerivAt_Fss_R (ks δ0 : ℝ) (s : ℂ) (R : ℝ) (hX : p.X ≠ 0)
    (h1 : s + p.an * ((R : ℂ) + p.X * I) ≠ 0) (h2 : s + p.an * ((R : ℂ) - p.X * I) ≠ 0) :
    HasDerivAt (fun R : ℝ => p.Fss ks δ0 s R) (p.FRR δ0 s R) R := by
  have hz1 : (R : ℂ) - p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hz2 : (R : ℂ) + p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hR : HasDerivAt (fun R : ℝ => (R : ℂ)) 1 R := by
    simpa using (hasDerivAt_id R).ofReal_comp
  have hi1 := ((((hR.add_const (p.X * I : ℂ)).const_mul (p.an : ℂ)).const_add s)).inv h1
  have hi2 := ((((hR.sub_const (p.X * I : ℂ)).const_mul (p.an : ℂ)).const_add s)).inv h2
  have hj1 := (hR.sub_const (p.X * I : ℂ)).inv hz1
  have hj2 := (hR.add_const (p.X * I : ℂ)).inv hz2
  have hKv := (hi1.add hi2).const_mul ((p.an : ℂ) * p.ma ^ 2 / 2)
  have hHj := (hi1.sub hi2).const_mul (I * ((p.an : ℂ) * p.ma ^ 2 / 2))
  have hP := ((hj1.const_mul (I * ((p.ma : ℂ) ^ 2 - p.V * p.φ δ0))).sub
    (hj2.const_mul (I * ((p.ma : ℂ) ^ 2 - p.V * p.φt δ0)))).div_const 2
  have h := ((hKv.const_mul s).const_add (p.C * s ^ 2 + ks : ℂ)).add ((hP.add hHj).const_mul (p.ωb : ℂ))
  convert h using 1
  · funext R
    simp only [Fss_eq, KvR, HjR, PθR, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    ring
  · simp only [FRR]
    ring

@[tmio M, powerlib_domain] theorem hasDerivAt_Fss_s (ks δ0 : ℝ) (s : ℂ) (R : ℝ)
    (h1 : s + p.an * ((R : ℂ) + p.X * I) ≠ 0) (h2 : s + p.an * ((R : ℂ) - p.X * I) ≠ 0) :
    HasDerivAt (fun s : ℂ => p.Fss ks δ0 s R) (p.FsR s R) s := by
  have hi1 := ((hasDerivAt_id s).add_const (p.an * ((R : ℂ) + p.X * I))).inv h1
  have hi2 := ((hasDerivAt_id s).add_const (p.an * ((R : ℂ) - p.X * I))).inv h2
  have hKv := (hi1.add hi2).const_mul ((p.an : ℂ) * p.ma ^ 2 / 2)
  have hHj := (hi1.sub hi2).const_mul (I * ((p.an : ℂ) * p.ma ^ 2 / 2))
  have h := (((((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul (p.C : ℂ)).add_const (ks : ℂ)).add
    ((hasDerivAt_id s).mul hKv)).add ((hHj.const_add (p.PθR δ0 R)).const_mul (p.ωb : ℂ))
  convert h using 1
  · funext s
    simp only [Fss_eq, KvR, HjR, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [FsR, KvR, Pi.add_apply, Pi.inv_apply, id_eq]
    ring

@[tmio M, powerlib_domain] theorem continuousAt_FRR (δ0 : ℝ) (v : ℝ × ℂ) (hX : p.X ≠ 0)
    (h1 : v.2 + p.an * ((v.1 : ℂ) + p.X * I) ≠ 0) (h2 : v.2 + p.an * ((v.1 : ℂ) - p.X * I) ≠ 0) :
    ContinuousAt (fun v : ℝ × ℂ => p.FRR δ0 v.2 v.1) v := by
  have hz1 : (v.1 : ℂ) - p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hz2 : (v.1 : ℂ) + p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  simp only [FRR]
  fun_prop (disch := simp [h1, h2, hz1, hz2])

@[tmio M, powerlib_domain] theorem continuousAt_FsR (v : ℝ × ℂ)
    (h1 : v.2 + p.an * ((v.1 : ℂ) + p.X * I) ≠ 0) (h2 : v.2 + p.an * ((v.1 : ℂ) - p.X * I) ≠ 0) :
    ContinuousAt (fun v : ℝ × ℂ => p.FsR v.2 v.1) v := by
  simp only [FsR, KvR]
  fun_prop (disch := simp [h1, h2])

/-- A differentiable root branch through the lossless mode exists: at a Hopf point
`C Ω² = k_s + ω_b K` of the base oscillator the mode `jΩ` is simple
(`F_s = 2CjΩ ≠ 0`, `FsR_zero`). -/
@[tmio M, powerlib_domain] theorem exists_branch (ks δ0 Ω : ℝ) (hX : p.X ≠ 0) (hC : p.C ≠ 0)
    (hΩ : Ω ≠ 0) (hμ : Ω ^ 2 ≠ p.ωb ^ 2)
    (hHopf : p.C * Ω ^ 2 = ks + p.ωb * (p.ma * p.V * Real.cos δ0 / p.X)) :
    ∃ lam : ℝ → ℂ, lam 0 = Ω * I ∧ (∀ᶠ R in 𝓝 (0 : ℝ), p.Fss ks δ0 (lam R) R = 0) ∧
      DifferentiableAt ℝ lam 0 := by
  obtain ⟨h1, h2⟩ := p.hopf_ne Ω hμ
  obtain ⟨e1, e2⟩ := p.an_link_zero hX
  have hu1 : ((0 : ℝ), (Ω : ℂ) * I).2 + p.an * ((((0 : ℝ), (Ω : ℂ) * I).1 : ℂ) + p.X * I) ≠ 0 := by
    simp only; rw [e1]; exact h1
  have hu2 : ((0 : ℝ), (Ω : ℂ) * I).2 + p.an * ((((0 : ℝ), (Ω : ℂ) * I).1 : ℂ) - p.X * I) ≠ 0 := by
    simp only; rw [e2, show (Ω : ℂ) * I + -(p.ωb * I) = Ω * I - p.ωb * I by ring]; exact h2
  have hev1 : ∀ᶠ v in 𝓝 ((0 : ℝ), (Ω : ℂ) * I), v.2 + p.an * ((v.1 : ℂ) + p.X * I) ≠ 0 :=
    ContinuousAt.eventually_ne (by fun_prop) hu1
  have hev2 : ∀ᶠ v in 𝓝 ((0 : ℝ), (Ω : ℂ) * I), v.2 + p.an * ((v.1 : ℂ) - p.X * I) ≠ 0 :=
    ContinuousAt.eventually_ne (by fun_prop) hu2
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  refine exists_root_branch₂ (f := fun R s => p.Fss ks δ0 s R) (fR := fun R s => p.FRR δ0 s R) (fs := fun R s => p.FsR s R)
    (hev1.and hev2 |>.mono fun v hv => p.hasDerivAt_Fss_R ks δ0 v.2 v.1 hX hv.1 hv.2)
    (hev1.and hev2 |>.mono fun v hv => p.hasDerivAt_Fss_s ks δ0 v.2 v.1 hv.1 hv.2)
    (p.continuousAt_FRR δ0 _ hX hu1 hu2) (p.continuousAt_FsR _ hu1 hu2) ?_ ?_
  · rw [p.FsR_zero _ hX h1 h2]
    simp [hCc, hΩc, I_ne_zero]
  · rw [p.Fss_zero _ _ _ hX h1 h2]
    have hH : (p.C : ℂ) * (Ω : ℂ) ^ 2 = ks + p.ωb * ((p.ma * p.V * Real.cos δ0 / p.X : ℝ) : ℂ) := by
      exact_mod_cast hHopf
    linear_combination ((p.C : ℂ) * Ω ^ 2) * I_sq - hH

/-- The network-resistance term of (14), unconditionally: at a Hopf point of the base oscillator
there is a differentiable mode `λ(R)` (`exists_branch`), and for it
`(1 + κ_dc) σ'(0)/Ω = −(1/X)(m_a/V) μ/(2 cos δ₀) · 1/(1 − μ²)`. -/
@[tmio M, powerlib_domain] theorem report14_resistance_branch (ks δ0 Ω : ℝ) (hX : p.X ≠ 0)
    (hC : p.C ≠ 0) (hΩ : Ω ≠ 0) (hμ : Ω ^ 2 ≠ p.ωb ^ 2) (hωb : p.ωb ≠ 0) (hma : p.ma ≠ 0)
    (hV : p.V ≠ 0) (hc : Real.cos δ0 ≠ 0)
    (hHopf : p.C * Ω ^ 2 = ks + p.ωb * (p.ma * p.V * Real.cos δ0 / p.X)) :
    ∃ lam : ℝ → ℂ, lam 0 = Ω * I ∧ (∀ᶠ R in 𝓝 (0 : ℝ), p.Fss ks δ0 (lam R) R = 0) ∧
      (1 + ks / (p.ωb * (p.ma * p.V * Real.cos δ0 / p.X))) * (-(deriv lam 0).re) / Ω =
        -(1 / p.X) * (p.ma / p.V) * ((Ω / p.ωb) / (2 * Real.cos δ0)) / (1 - (Ω / p.ωb) ^ 2) := by
  obtain ⟨lam, h0, hroot, hd⟩ := p.exists_branch ks δ0 Ω hX hC hΩ hμ hHopf
  refine ⟨lam, h0, hroot, ?_⟩
  exact p.report14_resistance ks Ω (δ := fun _ => δ0) (d := 0) hX hC hΩ hμ hωb hma hV hc
    (hasDerivAt_const 0 δ0) hd.hasDerivAt h0 hroot

end Model
end MatchingNetwork
end powerlib.GFM
