import theorem.ParametricResonance.ElementDecomposition
import theorem.ParametricResonance.ThirdOrderCore
import theorem.Dynamics.Coordinates

/-! # dVOC with a DC bus: Jacobian, modulation and the 2:1 pump coefficient at the Hopf point

The synchronization core of a dispatchable virtual oscillator with a DC link and a DC-voltage PI
loop under a grid-angle modulation: the Jacobian, the three modulable elements (Lemma 1), the
modulation `A₁` with the DC-bus bilinearity, and, at the normalized Hopf point, the eigentriple,
the forced response, the weights of Table 4, the `δ`-column sum (15), the kinematic factor of
Table 6 and the pump coefficient (25).

Model boundary.
* State `x = (δ, v_dc, x_I) : Dynamics.State 3` (oscillator angle, DC-link voltage in pu, PI
  integrator), grid angle `θ` as input, continuous time; the amplitude loop is eliminated
  (`E = 1`), as in the source:
  `δ̇ = η (P₀ + k_p (v_dc − 1) + k_i x_I − p(δ − θ))`, `C v̇_dc = P₀ − p(δ − θ)/v_dc`,
  `ẋ_I = v_dc − 1` (`field`), with the DC source `I_in = P₀`.
* `p(Ψ)` is the port power as a static map of the relative angle (quasi-static network);
  `K = p'(Ψ₀)`, `p''(Ψ₀) = −τ_δ K` (curvature ratio `τ_δ`), equilibrium `p(Ψ₀) = P₀`, `v_dc = 1`.
  Excluded: amplitude dynamics, delay, inner loops, current limiting, PWM, network dynamics.
* Normalized Hopf point (time unit `1/Ω_m`): `ν_δ = ηK`, `ν_P = P₀/C`, `ν_K = K/C`, the PI gains
  fixed by `d₁ = Ω_m² = 1` and `d₀ = d₂` (`hopfMatrix`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (dVOC core, `D_dVOC`), Table 4 (dVOC weights), (15),
Table 5 (modulable elements `(δ,δ)`, `(v_dc,δ)`, `(v_dc,v_dc)`), Table 6 (`S_m`), (25), Table 9
(dVOC row, `ρ` entries and `ĝ = (4/3)|N|/|𝒟|`), §8 ("dVOC 的闭式").

Results.
* `hasFDerivAt_field`, `hasDerivAt_field_input` — the Jacobian `jacobian (p Ψ) K v` and the input
  vector `B = (ηK, K/(C v), 0)`.
* `jacAt_const` — every entry except `(δ,δ)`, `(v_dc,δ)`, `(v_dc,v_dc)` is constant (Lemma 1).
* `modulation_eq` — `A₁` (`modMatrix`): `(δ,δ) = −η p'' z_Ψ`, `(v_dc,δ) = −(p''/C) z_Ψ + (K/C) z_v`,
  `(v_dc,v_dc) = (K/C) z_Ψ − (2P₀/C) z_v`, `z_Ψ = z_δ − 1`; hence the ratios of Table 9:
  `ratio_00`, `ratio_10`, `ratio_11` (`ρ = τ_δ S`, `τ_δ S − z_v`, `−χ_δ S − 2 z_v`).
* `jacobian_equilibrium` — at the equilibrium the Jacobian and `A₁` are the normalized matrices
  `hopfMatrix`, `hopfMod` under `ν_δ = ηK`, `ν_P = P₀/C`, `ν_K = K/C`.
* Normalized Hopf point: `charPoly_hopf` (`D(s) = (s + ν_i)(s² + 1)`, `ν_i = ν_δ − ν_P`),
  `right_eig`, `left_eig`, `left_right`, `forced_eq` (at `s = 2j`), `sensitivity_eq`
  (`S = (4/3)(2j − ν_P)/(2j + ν_i)`), `weight_00`, `weight_10`, `weight_11` (Table 4),
  `column_sum` (15), `pump_eq` (`g = −(2/3) N/𝒟` in the normalization `r_{x_I} = 1`),
  `normalizedPump_eq` (`ĝ = (4/3)|N|/|𝒟|`, independent of the eigenvector phase).

Corrections.
* (25) states `g_m/Ω_m = (2/3) N/𝒟`. The phase of `g_m` depends on the phase normalization of the
  eigenvector (`Element.pump_rescale`); in the normalization `r_{x_I} = 1` the value is
  `−(2/3) N/𝒟`. The modulus, and hence `ĝ_m = (4/3)|N|/|𝒟|` and the threshold, agree with the
  source.

Family and connection conclusions.
None: static evidence on the dVOC core (Jacobian, modulation, eigentriple, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
open powerlib.Dynamics (State mk3 state3_ext toEuclideanCLM_apply3)
open Complex ComplexConjugate Matrix

/-- Parameters of the dVOC core with a DC link and an arbitrary port-power map. -/
structure DVOCCore where
  η : ℝ
  C : ℝ
  P0 : ℝ
  kp : ℝ
  ki : ℝ
  p : ℝ → ℝ

namespace DVOCCore

/-- Quotient rule for a scalar quotient of two differentiable scalar maps. -/
@[tmio T, powerlib_foundation] private theorem hasFDerivAt_div' {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {c e : E → ℝ} {c' e' : E →L[ℝ] ℝ} {x : E}
    (hc : HasFDerivAt c c' x) (he : HasFDerivAt e e' x) (hx : e x ≠ 0) :
    HasFDerivAt (fun y => c y / e y) ((e x)⁻¹ • c' - (c x / e x ^ 2) • e') x := by
  have hi := (hasFDerivAt_inv hx).comp x he
  have h := hc.mul hi
  convert h using 1
  · funext y; simp [div_eq_mul_inv]
  · ext v
    simp
    field_simp
    ring

variable (d : DVOCCore)

/-- The dVOC core field with grid angle `θ`. -/
def field (θ : ℝ) (x : State 3) : State 3 :=
  mk3 (d.η * (d.P0 + d.kp * (x 1 - 1) + d.ki * x 2 - d.p (x 0 - θ)))
    ((d.P0 - d.p (x 0 - θ) / x 1) / d.C) (x 1 - 1)

/-- The Jacobian at power `P = p(Ψ)`, slope `K = p'(Ψ)` and DC voltage `v`. -/
def jacobian (P K v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(d.η * K), d.η * d.kp, d.η * d.ki; -(K / (d.C * v)), P / (d.C * v ^ 2), 0; 0, 1, 0]

/-- The input vector `B = ∂f/∂θ`. -/
def inputVec (K v : ℝ) : Fin 3 → ℝ := ![d.η * K, K / (d.C * v), 0]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field {θ K : ℝ} {x : State 3}
    (hP : HasDerivAt d.p K (x 0 - θ)) (hv : x 1 ≠ 0) :
    HasFDerivAt (d.field θ)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (d.jacobian (d.p (x 0 - θ)) K (x 1))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hs := hP.comp_hasFDerivAt x (h0.sub_const θ)
  fin_cases i
  · have h := ((((hasFDerivAt_const d.P0 x).add ((h1.sub_const 1).const_mul d.kp)).add
      (h2.const_mul d.ki)).sub hs).const_mul d.η
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
      ring
  · have h := HasFDerivAt.const_mul ((hasFDerivAt_const d.P0 x).sub (hasFDerivAt_div' hs h1 hv))
      d.C⁻¹
    convert h using 1
    · funext y; simp [field, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
      field_simp
      ring
  · have h := h1.sub_const 1
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]

@[tmio M, powerlib_domain] theorem hasDerivAt_field_input {θ K : ℝ} {x : State 3}
    (hP : HasDerivAt d.p K (x 0 - θ)) (i : Fin 3) :
    HasDerivAt (fun θ => d.field θ x i) (d.inputVec K (x 1) i) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => x 0 - θ) (-1) θ := by
    simpa using (hasDerivAt_id θ).const_sub (x 0)
  have hc := hP.comp θ h1
  fin_cases i
  · have h := ((hasDerivAt_const θ (d.P0 + d.kp * (x 1 - 1) + d.ki * x 2)).sub hc).const_mul d.η
    convert h using 1
    · funext θ; simp [field]
    · simp [inputVec]
  · have h := ((hasDerivAt_const θ d.P0).sub (hc.div_const (x 1))).div_const d.C
    convert h using 1
    · funext θ; simp [field]
    · simp [inputVec]; field_simp
  · simpa [field, inputVec] using hasDerivAt_const θ (x 1 - 1)

/-! ## Modulable elements and the modulation `A₁` -/

/-- The Jacobian at the point `(x, θ)`. -/
def jacAt (q : State 3 × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  d.jacobian (d.p (q.1 0 - q.2)) (deriv d.p (q.1 0 - q.2)) (q.1 1)

/-- Lemma 1 for the dVOC core: only `(δ,δ)`, `(v_dc,δ)` and `(v_dc,v_dc)` can be modulated. -/
@[tmio M, powerlib_domain] theorem jacAt_const {i k : Fin 3}
    (h : ¬ ((i = 0 ∧ k = 0) ∨ (i = 1 ∧ k = 0) ∨ (i = 1 ∧ k = 1))) :
    ∃ c : ℝ, ∀ q, d.jacAt q i k = c := by
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;> simp [jacAt, jacobian]

/-- The modulation matrix at the equilibrium (`v_dc = 1`, `p(Ψ₀) = P₀`), `P₂ = p''(Ψ₀)`. -/
def modMatrix (K P2 : ℝ) (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-(d.η * P2) : ℝ) * (z 0 - 1), 0, 0;
    (-(P2 / d.C) : ℝ) * (z 0 - 1) + (K / d.C : ℝ) * z 1,
      (K / d.C : ℝ) * (z 0 - 1) - (2 * d.P0 / d.C : ℝ) * z 1, 0; 0, 0, 0]

/-- `A₁` of the dVOC core along the forced direction `(z⁽¹⁾, θ̂ = 1)` at the equilibrium. -/
@[tmio M, powerlib_domain] theorem modulation_eq {x : State 3} {θ K P2 : ℝ} (hC : d.C ≠ 0)
    (hx1 : x 1 = 1) (hpe : d.p (x 0 - θ) = d.P0) (hP : HasDerivAt d.p K (x 0 - θ))
    (hP2 : HasDerivAt (deriv d.p) P2 (x 0 - θ)) (z : Fin 3 → ℂ) :
    ParametricResonance.Element.modulation d.jacAt (x, θ)
        (WithLp.toLp 2 (fun i => (z i).re), 1) (WithLp.toLp 2 (fun i => (z i).im), 0) =
      d.modMatrix K P2 z := by
  have hK : deriv d.p (x 0 - θ) = K := hP.deriv
  have hL := ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).hasFDerivAt.comp (x, θ)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, θ)))).sub (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, θ)))
  have hV := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt.comp
    (x, θ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, θ)))
  have hdp := hP2.comp_hasFDerivAt (x, θ) hL
  have hp := hP.comp_hasFDerivAt (x, θ) hL
  have h00 := hdp.const_mul (-d.η)
  have h10 := (hasFDerivAt_div' hdp (hV.const_mul d.C) (by simpa [hx1] using hC)).neg
  have h11 := hasFDerivAt_div' hp ((hV.pow 2).const_mul d.C) (by simp [hx1, hC])
  have e00 : HasFDerivAt (fun q : State 3 × ℝ => d.jacAt q 0 0) _ (x, θ) :=
    h00.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp [jacAt, jacobian])
  have e10 : HasFDerivAt (fun q : State 3 × ℝ => d.jacAt q 1 0) _ (x, θ) :=
    h10.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
      simp [jacAt, jacobian])
  have e11 : HasFDerivAt (fun q : State 3 × ℝ => d.jacAt q 1 1) _ (x, θ) :=
    h11.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp [jacAt, jacobian])
  ext i k
  by_cases hik : (i = 0 ∧ k = 0) ∨ (i = 1 ∧ k = 0) ∨ (i = 1 ∧ k = 1)
  · rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [ParametricResonance.Element.modulation]
      rw [e00.fderiv]
      apply Complex.ext <;> simp [modMatrix] <;> ring
    · simp only [ParametricResonance.Element.modulation]
      rw [e10.fderiv]
      have hz0 := Complex.re_add_im (z 0)
      have hz1 := Complex.re_add_im (z 1)
      simp [modMatrix, hx1, hK]
      conv_rhs => rw [← hz0, ← hz1]
      field_simp
      ring
    · simp only [ParametricResonance.Element.modulation]
      rw [e11.fderiv]
      have hz0 := Complex.re_add_im (z 0)
      have hz1 := Complex.re_add_im (z 1)
      simp [modMatrix, hx1, hpe]
      conv_rhs => rw [← hz0, ← hz1]
      field_simp
      ring
  · obtain ⟨c, hc⟩ := d.jacAt_const hik
    rw [ParametricResonance.Element.modulation_eq_zero_of_const hc]
    fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> simp [modMatrix]

/-- Table 9, `(δ,δ)`: `ρ = τ_δ S` with `τ_δ = −p''/K`, `S = 1 − z_δ`. -/
@[tmio M, powerlib_domain] theorem ratio_00 {K P2 : ℝ} (hη : d.η ≠ 0) (hK : K ≠ 0)
    (z : Fin 3 → ℂ) :
    ParametricResonance.Element.ratio (Linear.complexify (d.jacobian d.P0 K 1))
        (d.modMatrix K P2 z) 0 0 = ((-P2 / K : ℝ) : ℂ) * (1 - z 0) := by
  have hη' : (d.η : ℂ) ≠ 0 := by exact_mod_cast hη
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  simp [ParametricResonance.Element.ratio, Linear.complexify, jacobian, modMatrix]
  field_simp
  ring

/-- Table 9, `(v_dc,δ)`: `ρ = τ_δ S − z_v`. -/
@[tmio M, powerlib_domain] theorem ratio_10 {K P2 : ℝ} (hC : d.C ≠ 0) (hK : K ≠ 0)
    (z : Fin 3 → ℂ) :
    ParametricResonance.Element.ratio (Linear.complexify (d.jacobian d.P0 K 1))
        (d.modMatrix K P2 z) 1 0 = ((-P2 / K : ℝ) : ℂ) * (1 - z 0) - z 1 := by
  have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  simp [ParametricResonance.Element.ratio, Linear.complexify, jacobian, modMatrix]
  field_simp
  ring

/-- Table 9, `(v_dc,v_dc)`: `ρ = −χ_δ S − 2 z_v`, `χ_δ = K/P₀`. -/
@[tmio M, powerlib_domain] theorem ratio_11 {K P2 : ℝ} (hC : d.C ≠ 0) (hP0 : d.P0 ≠ 0)
    (z : Fin 3 → ℂ) :
    ParametricResonance.Element.ratio (Linear.complexify (d.jacobian d.P0 K 1))
        (d.modMatrix K P2 z) 1 1 = -((K / d.P0 : ℝ) : ℂ) * (1 - z 0) - 2 * z 1 := by
  have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hP0' : (d.P0 : ℂ) ≠ 0 := by exact_mod_cast hP0
  simp [ParametricResonance.Element.ratio, Linear.complexify, jacobian, modMatrix]
  field_simp
  ring

/-! ## The normalized Hopf point -/

/-- The normalized Jacobian at the Hopf point (`Ω_m = 1`). -/
def hopfMatrix (νδ νP νK : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-νδ, (1 + νδ * νP) / νK, (νδ - νP) / νK; -νK, νP, 0; 0, 1, 0]

/-- The normalized input vector. -/
def hopfInput (νδ νK : ℝ) : Fin 3 → ℂ := ![(νδ : ℂ), νK, 0]

/-- The normalized modulation (`p'' = −τ K`). -/
def hopfMod (νδ νP νK τ : ℝ) (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(νδ * τ : ℝ) * (z 0 - 1), 0, 0; (νK * τ : ℝ) * (z 0 - 1) + (νK : ℂ) * z 1,
    (νK : ℂ) * (z 0 - 1) - (2 * νP : ℝ) * z 1, 0; 0, 0, 0]

/-- The physical Jacobian, input and modulation at the equilibrium are the normalized ones. -/
@[tmio M, powerlib_domain] theorem jacobian_equilibrium {K τ νδ νP νK : ℝ} (hδ : d.η * K = νδ) (hP : d.P0 / d.C = νP) (hK : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (z : Fin 3 → ℂ) :
    d.jacobian d.P0 K 1 = hopfMatrix νδ νP νK ∧
      (fun i => ((d.inputVec K 1 i : ℝ) : ℂ)) = hopfInput νδ νK ∧
      d.modMatrix K (-(τ * K)) z = hopfMod νδ νP νK τ z := by
  refine ⟨?_, ?_, ?_⟩
  · ext i k; fin_cases i <;> fin_cases k <;> simp [jacobian, hopfMatrix, hδ, hkp, hki, ← hK, ← hP]
  · funext i; fin_cases i <;> simp [inputVec, hopfInput, hδ, ← hK]
  · subst hδ hK hP
    ext i k; fin_cases i <;> fin_cases k <;>
      simp [modMatrix, hopfMod, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> field_simp

/-- `det(sI − A₀) = (s + ν_i)(s² + 1)`, `ν_i = ν_δ − ν_P`. -/
@[tmio M, powerlib_domain] theorem charPoly_hopf {νδ νP νK : ℝ} (hνK : νK ≠ 0) (s : ℂ) :
    (Linear.characteristicMatrix (hopfMatrix νδ νP νK) s).det =
      (s + ((νδ - νP : ℝ) : ℂ)) * (s ^ 2 + 1) := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  simp [Linear.characteristicMatrix, hopfMatrix, Matrix.det_fin_three]
  field_simp
  ring

/-- Right eigenvector of `λ = j`: `((1 + jν_P)/ν_K, j, 1)`. -/
def right (νP νK : ℝ) : Fin 3 → ℂ := ![(1 + (νP : ℂ) * I) / νK, I, 1]

/-- Left eigenvector of `λ = j`, normalized against `right`. -/
def left (νδ νP νK : ℝ) : Fin 3 → ℂ :=
  ![-I * νK / (2 * ((νP : ℂ) - νδ - I)), I * ((νδ : ℂ) + I) / (2 * ((νP : ℂ) - νδ - I)),
    ((νP : ℂ) - νδ) / (2 * ((νP : ℂ) - νδ - I))]

/-- The forced response at `s = 2j`. -/
def forced (νδ νP νK : ℝ) : Fin 3 → ℂ :=
  ![-((νP : ℂ) + 3 * νδ - 2 * I) / (3 * ((νP : ℂ) - νδ - 2 * I)),
    -4 * (νK : ℂ) / (3 * ((νP : ℂ) - νδ - 2 * I)), 2 * I * νK / (3 * ((νP : ℂ) - νδ - 2 * I))]

@[tmio T, powerlib_foundation] private theorem den1_ne (νδ νP : ℝ) : (νP : ℂ) - νδ - I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

@[tmio T, powerlib_foundation] private theorem den2_ne (νδ νP : ℝ) : (νP : ℂ) - νδ - 2 * I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

@[tmio M, powerlib_domain] theorem right_eig {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    Linear.complexify (hopfMatrix νδ νP νK) *ᵥ right νP νK = I • right νP νK := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  funext i
  fin_cases i
  · simp [Linear.complexify, hopfMatrix, right, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring_nf
    simp [I_sq]
  · simp [Linear.complexify, hopfMatrix, right, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring_nf
  · simp [Linear.complexify, hopfMatrix, right, mulVec, dotProduct, Fin.sum_univ_three]

@[tmio M, powerlib_domain] theorem left_eig {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    vecMul (left νδ νP νK) (Linear.complexify (hopfMatrix νδ νP νK)) = I • left νδ νP νK := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 := den1_ne νδ νP
  funext i
  fin_cases i
  · simp [Linear.complexify, hopfMatrix, left, vecMul, dotProduct, Fin.sum_univ_three]
    field_simp
    ring_nf
  · simp [Linear.complexify, hopfMatrix, left, vecMul, dotProduct, Fin.sum_univ_three]
    field_simp
    ring_nf
    simp [I_sq]
    ring
  · simp [Linear.complexify, hopfMatrix, left, vecMul, dotProduct, Fin.sum_univ_three]
    field_simp
    ring_nf

@[tmio M, powerlib_domain] theorem left_right {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    left νδ νP νK ⬝ᵥ right νP νK = 1 := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 := den1_ne νδ νP
  simp [left, right, dotProduct, Fin.sum_univ_three]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- `(2jI − A₀) z⁽¹⁾ = B` at the normalized Hopf point. -/
@[tmio M, powerlib_domain] theorem forced_eq {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    Linear.characteristicMatrix (hopfMatrix νδ νP νK) (2 * I) *ᵥ forced νδ νP νK =
      hopfInput νδ νK := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h2 := den2_ne νδ νP
  funext i
  fin_cases i
  · simp [Linear.characteristicMatrix, hopfMatrix, forced, hopfInput, mulVec, dotProduct,
      Fin.sum_univ_three]
    field_simp
    ring_nf
    simp [I_sq]
    ring
  · simp [Linear.characteristicMatrix, hopfMatrix, forced, hopfInput, mulVec, dotProduct,
      Fin.sum_univ_three]
    field_simp
    ring_nf
  · simp [Linear.characteristicMatrix, hopfMatrix, forced, hopfInput, mulVec, dotProduct,
      Fin.sum_univ_three]
    field_simp
    ring_nf
    simp [I_sq]

/-- Table 6, dVOC row: `S = 1 − z_δ = −z_Ψ = (4/3)(2j − ν_P)/(2j + ν_i)`, which is the pole–zero
factor of `theorem/ParametricResonance/ThirdOrderCore.lean`. -/
@[tmio M, powerlib_domain] theorem sensitivity_eq (νδ νP νK : ℝ) :
    1 - forced νδ νP νK 0 = ParametricResonance.ThirdOrder.poleZeroFactor (νδ - νP) 1 νP (2 * I) := by
  have hp := ParametricResonance.ThirdOrder.poleZeroFactor_hopf (d2 := νδ - νP) (a := νP)
    (one_ne_zero (α := ℝ))
  simp only [Complex.ofReal_one, mul_one] at hp
  rw [hp]
  have h2 := den2_ne νδ νP
  have h3 : (2 : ℂ) * I + ((νδ : ℂ) - νP) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h3' : I * 2 + ((νδ : ℂ) - νP) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h2' : (νP : ℂ) - νδ - I * 2 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp [forced]
  field_simp
  ring

/-- Table 4, `(δ,δ)`: `w = ν_δ (ν_P − j)/(2(ν_i + j))`. -/
@[tmio M, powerlib_domain] theorem weight_00 {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (hopfMatrix νδ νP νK))
        (left νδ νP νK) (right νP νK) 0 0 =
      (νδ : ℂ) * ((νP : ℂ) - I) / (2 * (((νδ - νP : ℝ) : ℂ) + I)) := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 := den1_ne νδ νP
  have h1' : (νδ : ℂ) - νP + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp [ParametricResonance.Element.weight, Linear.complexify, hopfMatrix, left, right]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- Table 4, `(v_dc,δ)`: `w = −(ν_δ + j)(ν_P − j)/(2(ν_i + j))`. -/
@[tmio M, powerlib_domain] theorem weight_10 {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (hopfMatrix νδ νP νK))
        (left νδ νP νK) (right νP νK) 1 0 =
      -(((νδ : ℂ) + I) * ((νP : ℂ) - I)) / (2 * (((νδ - νP : ℝ) : ℂ) + I)) := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 := den1_ne νδ νP
  have h1' : (νδ : ℂ) - νP + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp [ParametricResonance.Element.weight, Linear.complexify, hopfMatrix, left, right]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- Table 4, `(v_dc,v_dc)`: `w = ν_P (ν_δ + j)/(2(ν_i + j))`. -/
@[tmio M, powerlib_domain] theorem weight_11 {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (hopfMatrix νδ νP νK))
        (left νδ νP νK) (right νP νK) 1 1 =
      (νP : ℂ) * ((νδ : ℂ) + I) / (2 * (((νδ - νP : ℝ) : ℂ) + I)) := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 := den1_ne νδ νP
  have h1' : (νδ : ℂ) - νP + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp [ParametricResonance.Element.weight, Linear.complexify, hopfMatrix, left, right]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- (15): `w_{δδ} + w_{v δ} = −(1 + jν_P)/(2(ν_i + j))`. -/
@[tmio M, powerlib_domain] theorem column_sum {νδ νP νK : ℝ} (hνK : νK ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (hopfMatrix νδ νP νK))
        (left νδ νP νK) (right νP νK) 0 0 +
      ParametricResonance.Element.weight (Linear.complexify (hopfMatrix νδ νP νK))
        (left νδ νP νK) (right νP νK) 1 0 =
      -(1 + (νP : ℂ) * I) / (2 * (((νδ - νP : ℝ) : ℂ) + I)) := by
  rw [weight_00 hνK, weight_10 hνK]
  have h1' : (νδ : ℂ) - νP + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  push_cast
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- The numerator `N = ν_K(1 − jν_δ) + jτ(ν_P + j)(ν_P − 2j)` of (25). -/
def numN (νδ νP νK τ : ℝ) : ℂ :=
  (νK : ℂ) * (1 - I * νδ) + I * τ * ((νP : ℂ) + I) * ((νP : ℂ) - 2 * I)

/-- The denominator `𝒟 = (ν_i + j)(ν_i + 2j)` of (25). -/
def denD (νδ νP : ℝ) : ℂ := (((νδ - νP : ℝ) : ℂ) + I) * (((νδ - νP : ℝ) : ℂ) + 2 * I)

/-- (25) in the normalization `r_{x_I} = 1`: `g = −(2/3) N/𝒟`. -/
@[tmio M, powerlib_domain] theorem pump_eq {νδ νP νK τ : ℝ} (hνK : νK ≠ 0) :
    ParametricResonance.Element.pump (hopfMod νδ νP νK τ (forced νδ νP νK)) (left νδ νP νK)
        (right νP νK) = -(2 / 3) * (numN νδ νP νK τ / denD νδ νP) := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 := den1_ne νδ νP
  have h2 := den2_ne νδ νP
  have hA : (νδ : ℂ) - νP + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hB : (νδ : ℂ) - νP + 2 * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hB' : (νδ : ℂ) - νP + I * 2 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h2' : (νP : ℂ) - νδ - I * 2 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp [ParametricResonance.Element.pump, hopfMod, forced, left, right, mulVec, dotProduct,
    Fin.sum_univ_three, numN, denD]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- Table 9, dVOC row: `ĝ = 2|g| = (4/3)|N|/|𝒟|`, for every phase normalization of the
eigenvectors (`Element.norm_pump_rescale`). -/
@[tmio M, powerlib_domain] theorem normalizedPump_eq {νδ νP νK τ : ℝ} (hνK : νK ≠ 0) {c : ℂ}
    (hc : c ≠ 0) :
    ParametricResonance.Element.normalizedPump
        (ParametricResonance.Element.pump (hopfMod νδ νP νK τ (forced νδ νP νK))
          (c⁻¹ • left νδ νP νK) (c • right νP νK)) 1 =
      4 / 3 * (‖numN νδ νP νK τ‖ / ‖denD νδ νP‖) := by
  rw [ParametricResonance.Element.normalizedPump, ParametricResonance.Element.norm_pump_rescale _ _ _ hc,
    pump_eq hνK, norm_mul, norm_neg, norm_div, norm_div]
  norm_num
  ring

end DVOCCore

end powerlib.GFM
