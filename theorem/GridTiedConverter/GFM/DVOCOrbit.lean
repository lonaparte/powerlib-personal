import theorem.GridTiedConverter.GFM.DVOCVoltage
import theorem.ParametricResonance.SmoothForcedOrbit

/-! # dVOC with a DC bus under grid-voltage modulation: forced orbit and Floquet multipliers of the nonlinear model

End-to-end statement for the dVOC core of `DVOCPump` with the port power scaled by the grid-voltage
magnitude (`DVOCVoltage`). The real field `rfieldV` is smooth wherever `v_dc ≠ 0`; its Jacobian,
second derivatives and voltage input are computed along lines (`line_rfieldV`, `line_jacV`), and at
the normalized Hopf point they are `hopfMatrix`, the modulation `hopfModV` and `B_V`. With the
third eigenvector of the real pole `ν_P − ν_δ`, `SmoothForcedOrbit` gives: for small `ε` the
forced orbit exists, and its Floquet multipliers are inside or outside the unit circle according to
`|g_V/2| ≶ |λ₁|`, `g_V = −(j V̂/(6ν_K V₀)) N_V/𝒟`.

Model boundary.
* `DVOCCore` with grid angle `0`, port power `(V/V₀) p(δ)` with `p` of class `C³`, DC source
  `P₀`, DC-voltage PI loop, amplitude loop eliminated (`rfieldV`); states `(δ, v_dc, x_I)`.
* Operating point `x₀ = (Ψ₀, 1, 0)` with `p(Ψ₀) = P₀`; normalized Hopf point (time unit `1/Ω_m`,
  `Ω = 1`, drive `V₀ + ε V̂ cos 2t`) with `ν_δ = ηK`, `ν_P = P₀/C`, `ν_K = K/C`, the PI gains of
  `hopfMatrix`, `p'' = −τK`, and `ν_P < ν_δ`; state perturbation `ε A₀'` with any real `A₀'`.
* The exponential stability of the nonlinear solutions near the orbit is in `GFMOrbitStability`,
  and the gain change `k_p → k_p + εk_{p1}` as the source of `A₀'` in `GFMParameterShift`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2, §3 (dVOC core), (25); the voltage excitation is new.

Results.
* `rfieldV`, `contDiffAt_rfieldV`, `line_rfieldV`, `matX_rfieldV` — the field, its smoothness and
  `∂ₓ rfieldV = jacV` where `v_dc ≠ 0`.
* `xeq`, `rfieldV_eq_zero`, `fderivW_rfieldV` (`∂_V F = inputV`), `dxMat`, `m1Mat`, `smDx_rfieldV`,
  `smM1_rfieldV`, `smA1_rfieldV` (`A₁ = modMatrixV`) — the data of the forced system.
* `right3`, `left3`, `right3_eig`, `left3_eig`, `left3_right3` — the real pole `ν_P − ν_δ`:
  `r₃ = (ν_δ λ₃/ν_K, λ₃, 1)`, `u₃ = (−ν_K, ν_P, 1)/(1 + λ₃²)`.
* `matX_hopf`, `zorb_hopf`, `pump_hopf` — at the normalized Hopf point.
* `orbit_voltage_stable`, `orbit_voltage_unstable` — the end-to-end Floquet statements.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated dVOC core (forced orbit, Floquet multipliers).
-/

noncomputable section

namespace powerlib.GFM
namespace DVOCCore
open Complex Matrix Filter Topology
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)

variable (d : DVOCCore)

/-- The dVOC core field in the states `x = (δ, v_dc, x_I)` (grid angle `0`) with the
grid-voltage magnitude `V` as input, port power `(V/V₀) p(δ)`. -/
def rfieldV (V0 : ℝ) (q : (Fin 3 → ℝ) × ℝ) : Fin 3 → ℝ :=
  ![d.η * (d.P0 + d.kp * (q.1 1 - 1) + d.ki * q.1 2 - q.2 / V0 * d.p (q.1 0)),
    (d.P0 - q.2 / V0 * d.p (q.1 0) / q.1 1) / d.C,
    q.1 1 - 1]

/-- The field is `Cⁿ` wherever `v_dc ≠ 0`, for a `Cⁿ` port-power map. -/
@[tmio M, powerlib_domain] theorem contDiffAt_rfieldV (V0 : ℝ) {n : WithTop ℕ∞}
    (hp : ContDiff ℝ n d.p) {x : Fin 3 → ℝ} {V : ℝ} (hx : x 1 ≠ 0) :
    ContDiffAt ℝ n (d.rfieldV V0) (x, V) := by
  have hc : ∀ i : Fin 3, ContDiffAt ℝ n (fun q : (Fin 3 → ℝ) × ℝ => q.1 i) (x, V) := fun i =>
    ((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffAt
  have hV : ContDiffAt ℝ n (fun q : (Fin 3 → ℝ) × ℝ => q.2) (x, V) := contDiff_snd.contDiffAt
  have hp0 : ContDiffAt ℝ n (fun q : (Fin 3 → ℝ) × ℝ => d.p (q.1 0)) (x, V) :=
    (hp.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_fst)).contDiffAt
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i
  · exact contDiffAt_const.mul ((((contDiffAt_const.add (contDiffAt_const.mul
      ((hc 1).sub contDiffAt_const))).add (contDiffAt_const.mul (hc 2))).sub
      ((hV.div_const V0).mul hp0)))
  · exact (contDiffAt_const.sub (((hV.div_const V0).mul hp0).div (hc 1) hx)).div_const _
  · exact (hc 1).sub contDiffAt_const

/-- The field along a line in the state: `d/ds f(x + s y, V) = jacV(x, V) y`. -/
@[tmio M, powerlib_domain] theorem line_rfieldV (V0 V : ℝ) (x y : Fin 3 → ℝ) (hx : x 1 ≠ 0)
    {K : ℝ} (hP : HasDerivAt d.p K (x 0)) :
    HasDerivAt (fun s : ℝ => d.rfieldV V0 (x + s • y, V))
      (d.jacV V0 V (d.p (x 0)) K (x 1) *ᵥ y) 0 := by
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (x + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (x i)
  have hp : HasDerivAt (fun s : ℝ => d.p ((x + s • y) 0)) (K * y 0) 0 :=
    HasDerivAt.comp_of_eq 0 hP (hl 0) (by simp)
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · have h := ((((hasDerivAt_const (0 : ℝ) d.P0).add (((hl 1).sub_const 1).const_mul d.kp)).add
      ((hl 2).const_mul d.ki)).sub (hp.const_mul (V / V0))).const_mul d.η
    convert h using 1
    · funext s; simp [rfieldV]
    · simp [jacV, jacobian, mulVec, dotProduct, Fin.sum_univ_three]; ring
  · have hne : (x + (0 : ℝ) • y) 1 ≠ 0 := by simpa using hx
    have h := ((hasDerivAt_const (0 : ℝ) d.P0).sub
      ((hp.const_mul (V / V0)).div (hl 1) hne)).div_const d.C
    convert h using 1
    · funext s; simp [rfieldV, mul_div_assoc]
    · simp [jacV, jacobian, mulVec, dotProduct, Fin.sum_univ_three]; field_simp; ring
  · have h := (hl 1).sub_const 1
    convert h using 1
    · funext s; simp [rfieldV]
    · simp [jacV, jacobian, mulVec, dotProduct, Fin.sum_univ_three]

/-- `∂ₓ rfieldV(x, V) = jacV(x, V)` wherever `v_dc ≠ 0`. -/
@[tmio M, powerlib_domain] theorem matX_rfieldV (V0 : ℝ) (hp : ContDiff ℝ 3 d.p) {x : Fin 3 → ℝ}
    {V : ℝ} (hx : x 1 ≠ 0) :
    matX (d.rfieldV V0) (x, V) = d.jacV V0 V (d.p (x 0)) (deriv d.p (x 0)) (x 1) :=
  ParametricResonance.ForcedOrbit.matX_of_line
    ((d.contDiffAt_rfieldV V0 hp hx).differentiableAt (by norm_num)) fun y =>
    d.line_rfieldV V0 V x y hx ((hp.differentiable (by norm_num) (x 0)).hasDerivAt)

/-- The equilibrium state `x₀ = (Ψ₀, 1, 0)`. -/
def xeq (Ψ0 : ℝ) : Fin 3 → ℝ := ![Ψ0, 1, 0]

@[tmio M, powerlib_domain] theorem rfieldV_eq_zero {V0 Ψ0 : ℝ} (hV0 : V0 ≠ 0)
    (hpe : d.p Ψ0 = d.P0) : d.rfieldV V0 (xeq Ψ0, V0) = 0 := by
  funext i
  fin_cases i <;> simp [rfieldV, xeq, hpe, div_self hV0]

/-- `∂_V rfieldV(x₀, V₀) = inputV`. -/
@[tmio M, powerlib_domain] theorem fderivW_rfieldV {V0 Ψ0 : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hpe : d.p Ψ0 = d.P0) :
    fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1) = d.inputV V0 := by
  refine ParametricResonance.ForcedOrbit.fderivW_of_line
    ((d.contDiffAt_rfieldV V0 hp (by simp [xeq])).differentiableAt (by norm_num)) ?_
  refine hasDerivAt_pi.2 fun i => ?_
  have hW : HasDerivAt (fun s : ℝ => (V0 + s) / V0) (1 / V0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add V0).div_const V0
  fin_cases i
  · have h := ((hasDerivAt_const (0 : ℝ) d.P0).sub (hW.mul_const d.P0)).const_mul d.η
    convert h using 1
    · funext s; simp [rfieldV, xeq, hpe]
    · simp [inputV]; ring
  · have h := ((hasDerivAt_const (0 : ℝ) d.P0).sub (hW.mul_const d.P0)).div_const d.C
    convert h using 1
    · funext s; simp [rfieldV, xeq, hpe]
    · simp [inputV]; ring
  · convert hasDerivAt_const (0 : ℝ) (0 : ℝ) using 1
    · funext s; simp [rfieldV, xeq]
    · simp [inputV]

/-- The real second derivative along a state direction at the equilibrium. -/
def dxMat (K P2 : ℝ) (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(d.η * (P2 * y 0)), 0, 0;
    -(P2 * y 0 / d.C) + K / d.C * y 1, K / d.C * y 0 - 2 * d.P0 / d.C * y 1, 0;
    0, 0, 0]

/-- The real mixed second derivative in the grid voltage at the equilibrium. -/
def m1Mat (V0 K : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(d.η * (K / V0)), 0, 0; -(K / V0 / d.C), d.P0 / d.C / V0, 0; 0, 0, 0]

@[tmio M, powerlib_domain] theorem smDx_rfieldV {V0 Ψ0 K P2 : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hV0 : V0 ≠ 0) (hC : d.C ≠ 0) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (y : Fin 3 → ℝ) :
    smDx (d.rfieldV V0) (xeq Ψ0, V0) y = d.dxMat K P2 y := by
  have hK : deriv d.p Ψ0 = K := hP.deriv
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), 1 + t * y 1 ≠ 0 :=
    (by fun_prop : Continuous fun t : ℝ => 1 + t * y 1).continuousAt.eventually_ne (by simp)
  obtain ⟨e00, e10, e11⟩ := d.line_jacV (zΨ := y 0) (zv := y 1) (zV := 0) hV0 hC hP hP2 hpe hK
  refine ParametricResonance.ForcedOrbit.smDx_of_line
    ((d.contDiffAt_rfieldV V0 hp (by simp [xeq])).of_le (by norm_num)) y
    (Jr := fun t => d.jacV V0 (V0 + t * 0) (d.p (Ψ0 + t * y 0)) (deriv d.p (Ψ0 + t * y 0))
      (1 + t * y 1)) (hne.mono fun t ht => ?_) fun i j => ?_
  · have hx : (xeq Ψ0 + t • y) 1 ≠ 0 := by simpa [xeq] using ht
    rw [d.matX_rfieldV V0 hp hx]
    simp [xeq]
  · fin_cases i <;> fin_cases j
    · exact e00.congr_deriv (by show _ = -(d.η * (P2 * y 0)); simp)
    · exact hasDerivAt_const (0 : ℝ) (d.η * d.kp)
    · exact hasDerivAt_const (0 : ℝ) (d.η * d.ki)
    · exact e10.congr_deriv (by show _ = -(P2 * y 0 / d.C) + K / d.C * y 1; simp)
    · exact e11.congr_deriv (by show _ = K / d.C * y 0 - 2 * d.P0 / d.C * y 1; simp)
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)

@[tmio M, powerlib_domain] theorem smM1_rfieldV {V0 Ψ0 K P2 : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hV0 : V0 ≠ 0) (hC : d.C ≠ 0) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) :
    smM1 (d.rfieldV V0) (xeq Ψ0, V0) = d.m1Mat V0 K := by
  have hK : deriv d.p Ψ0 = K := hP.deriv
  obtain ⟨e00, e10, e11⟩ := d.line_jacV (zΨ := 0) (zv := 0) (zV := 1) hV0 hC hP hP2 hpe hK
  refine ParametricResonance.ForcedOrbit.smM1_of_line
    ((d.contDiffAt_rfieldV V0 hp (by simp [xeq])).of_le (by norm_num))
    (Jr := fun t => d.jacV V0 (V0 + t * 1) (d.p (Ψ0 + t * 0)) (deriv d.p (Ψ0 + t * 0))
      (1 + t * 0)) (Filter.Eventually.of_forall fun t => ?_) fun i j => ?_
  · rw [d.matX_rfieldV V0 hp (by simp [xeq])]
    simp [xeq]
  · fin_cases i <;> fin_cases j
    · exact e00.congr_deriv (by show _ = -(d.η * (K / V0)); simp)
    · exact hasDerivAt_const (0 : ℝ) (d.η * d.kp)
    · exact hasDerivAt_const (0 : ℝ) (d.η * d.ki)
    · exact e10.congr_deriv (by show _ = -(K / V0 / d.C); simp)
    · exact e11.congr_deriv (by show _ = d.P0 / d.C / V0; simp)
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-- The modulation of the real field along `(z, V̂)` is `modMatrixV` of `DVOCVoltage`. -/
@[tmio M, powerlib_domain] theorem smA1_rfieldV {V0 Ψ0 K P2 : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hV0 : V0 ≠ 0) (hC : d.C ≠ 0) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (Vh : ℝ) (z : Fin 3 → ℂ) :
    smA1 (d.rfieldV V0) (xeq Ψ0, V0) Vh z = d.modMatrixV V0 K P2 Vh z := by
  have hdx := d.smDx_rfieldV hp hV0 hC hpe hP hP2
  have hm := d.smM1_rfieldV hp hV0 hC hpe hP hP2
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [dxMat, m1Mat, modMatrixV, -Complex.ofReal_mul, -Complex.ofReal_div,
      -Complex.ofReal_inv] <;> ring

/-- Right eigenvector of the real pole `λ₃ = ν_P − ν_δ` at the normalized Hopf point. -/
def right3 (νδ νP νK : ℝ) : Fin 3 → ℝ := ![νδ * (νP - νδ) / νK, νP - νδ, 1]

/-- Left eigenvector of `λ₃`, normalized against `right3`. -/
def left3 (νδ νP νK : ℝ) : Fin 3 → ℝ :=
  ![-νK / (1 + (νP - νδ) ^ 2), νP / (1 + (νP - νδ) ^ 2), 1 / (1 + (νP - νδ) ^ 2)]

omit d in
@[tmio M, powerlib_domain] theorem right3_eig {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    hopfMatrix νδ νP νK *ᵥ right3 νδ νP νK = (νP - νδ) • right3 νδ νP νK := by
  funext i
  fin_cases i <;> simp [hopfMatrix, right3, mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;> ring

omit d in
@[tmio M, powerlib_domain] theorem left3_eig {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    left3 νδ νP νK ᵥ* hopfMatrix νδ νP νK = (νP - νδ) • left3 νδ νP νK := by
  have hpos : (1 + (νP - νδ) ^ 2) ≠ 0 := by positivity
  funext i
  fin_cases i <;> simp [hopfMatrix, left3, vecMul, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;> ring

omit d in
@[tmio M, powerlib_domain] theorem left3_right3 {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    left3 νδ νP νK ⬝ᵥ right3 νδ νP νK = 1 := by
  have hpos : (1 + (νP - νδ) ^ 2) ≠ 0 := by positivity
  simp [left3, right3, dotProduct, Fin.sum_univ_three]
  field_simp
  ring

/-- At the normalized Hopf point the partial Jacobian of the real field is `hopfMatrix`. -/
@[tmio M, powerlib_domain] theorem matX_hopf {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) :
    matX (d.rfieldV V0) (xeq Ψ0, V0) = hopfMatrix νδ νP νK := by
  rw [d.matX_rfieldV V0 hp (by simp [xeq] : xeq Ψ0 1 ≠ 0)]
  have e : d.jacV V0 V0 (d.p (xeq Ψ0 0)) (deriv d.p (xeq Ψ0 0)) (xeq Ψ0 1) =
      d.jacobian d.P0 K 1 := by
    simp [xeq, jacV, hpe, hP.deriv, div_self hV0]
  rw [e, (d.jacobian_equilibrium (τ := 0) hδ hPn hKn hνK hkp hki 0).1]

/-- The first-order orbit of the voltage drive at `2Ω = 2`:
`z = −(V̂/V₀)(ν_P/ν_K) z⁽¹⁾` solves `(2jI − ∂ₓF) z = V̂ ∂_V F`. -/
@[tmio M, powerlib_domain] theorem zorb_hopf {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (Vh : ℝ) :
    (((2 * 1 : ℝ) : ℂ) * I) • ((-(Vh / V0 * νP / νK) : ℝ) • forced νδ νP νK) -
        (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
          ((-(Vh / V0 * νP / νK) : ℝ) • forced νδ νP νK) =
      (Vh : ℂ) • fun i => ((fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1) i : ℝ) : ℂ) := by
  rw [d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0, d.fderivW_rfieldV hp hpe,
    (d.voltage_equilibrium (τ := 0) (vh := 0) hδ hPn hKn hνK hV0 0).2.1]
  have hc : ((-(Vh / V0 * νP / νK) : ℝ) • forced νδ νP νK) =
      (((-(Vh / V0 * νP / νK) : ℝ) : ℂ)) • forced νδ νP νK := by
    funext i; simp [Complex.real_smul]
  have hf := forcedV_eq (νδ := νδ) (νP := νP) hνK (((-(Vh / V0 * νP / νK) : ℝ) : ℂ))
  rw [Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hf
  rw [hc, show (((2 * 1 : ℝ) : ℂ) * I) = 2 * I by push_cast; ring]
  rw [hf, smul_smul]
  congr 1
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have hV0' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  push_cast
  field_simp

/-- The pump of the real field along the first-order orbit is the closed form of `DVOCVoltage`:
`u A₁ r̄ = −(j v/(6ν_K)) N_V/𝒟`, `v = V̂/V₀`. -/
@[tmio M, powerlib_domain] theorem pump_hopf {V0 Ψ0 K P2 τ νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p)
    (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0) (hP2 : HasDerivAt (deriv d.p) P2 Ψ0)
    (hτ : P2 = -(τ * K)) (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK)
    (hνK : νK ≠ 0) (hV0 : V0 ≠ 0) (Vh : ℝ) :
    left νδ νP νK ⬝ᵥ (smA1 (d.rfieldV V0) (xeq Ψ0, V0) Vh
      ((-(Vh / V0 * νP / νK) : ℝ) • forced νδ νP νK) *ᵥ star (right νP νK)) =
      -(I * ((Vh / V0 : ℝ) : ℂ) / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) := by
  have hC : d.C ≠ 0 := by rintro h; apply hνK; rw [← hKn, h, div_zero]
  rw [d.smA1_rfieldV hp hV0 hC hpe hP hP2, hτ,
    (d.voltage_equilibrium hδ hPn hKn hνK hV0 _).2.2, ← pumpV_eq hνK (Vh / V0)]
  rfl

/-- dVOC with a DC bus, grid-voltage modulation, end-to-end, stability (normalized Hopf point,
time unit `1/Ω_m`). The real three-state field `rfieldV` (`(V/V₀) p(δ)`, `p` of class `C³`) at
the equilibrium `x₀ = (Ψ₀, 1, 0)` is driven by `V = V₀ + ε V̂ cos 2t` and perturbed by `ε A₀'`.
With `ν_P < ν_δ` (third pole `ν_P − ν_δ < 0`), `Re λ₁ < 0` and `|g_V/2| < |λ₁|`
(`λ₁ = u A₀' r`, `g_V = −(j V̂/(6ν_K V₀)) N_V/𝒟`), for all small `ε > 0` the forced periodic orbit
exists (unique in the ball of radius `cε`) and all its Floquet multipliers lie inside the unit
circle. -/
@[tmio M, powerlib_domain] theorem orbit_voltage_stable {V0 Ψ0 K P2 τ νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (hτ : P2 = -(τ * K)) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖-(I * ((Vh / V0 : ℝ) : ℂ) / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) / 2‖ ^ 2 <
      ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) ∧
        (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (d.rfieldV V0 (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t))) +
          ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (d.rfieldV V0 (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t))) +
          ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (d.rfieldV V0) (xeq Ψ0, V0) Vh 2 A0' ε t (y t))
            (2 * Real.pi / 2) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hm := d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0
  have hmc : (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) =
      Linear.complexify (hopfMatrix νδ νP νK) := by rw [hm]
  have h := ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_stable
    (d.contDiffAt_rfieldV V0 hp (by simp [xeq])) (rfieldV_eq_zero d hV0 hpe)
    (Ω := 1) (Vh := Vh) one_pos (l3 := νP - νδ) (by linarith)
    (by rw [hmc]; simpa using right_eig hνK) (by rw [hmc]; simpa using left_eig hνK)
    (left_right hνK) (by rw [hm]; exact right3_eig hνK) (by rw [hm]; exact left3_eig hνK)
    (left3_right3 hνK) (d.zorb_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0 Vh) A0' hs
    (by rw [d.pump_hopf hp hpe hP hP2 hτ hδ hPn hKn hνK hV0 Vh]; exact hg)
  simpa only [mul_one] using h

/-- dVOC with a DC bus, grid-voltage modulation, end-to-end, parametric instability:
`|λ₁| < |g_V/2|` makes the forced periodic orbit Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_voltage_unstable {V0 Ψ0 K P2 τ νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (hτ : P2 = -(τ * K)) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2 <
      ‖-(I * ((Vh / V0 : ℝ) : ℂ) / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) ∧
        (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (d.rfieldV V0 (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t))) +
          ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (d.rfieldV V0 (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t))) +
          ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (d.rfieldV V0) (xeq Ψ0, V0) Vh 2 A0' ε t (y t))
          (2 * Real.pi / 2) := by
  have hm := d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0
  have hmc : (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) =
      Linear.complexify (hopfMatrix νδ νP νK) := by rw [hm]
  have h := ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_unstable
    (d.contDiffAt_rfieldV V0 hp (by simp [xeq])) (rfieldV_eq_zero d hV0 hpe)
    (Ω := 1) (Vh := Vh) one_pos (l3 := νP - νδ) (by linarith)
    (by rw [hmc]; simpa using right_eig hνK) (by rw [hmc]; simpa using left_eig hνK)
    (left_right hνK) (by rw [hm]; exact right3_eig hνK) (by rw [hm]; exact left3_eig hνK)
    (left3_right3 hνK) (d.zorb_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0 Vh) A0'
    (by rw [d.pump_hopf hp hpe hP hP2 hτ hδ hPn hKn hνK hV0 Vh]; exact hg)
  simpa only [mul_one] using h

end DVOCCore
end powerlib.GFM
