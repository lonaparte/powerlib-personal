import theorem.GridTiedConverter.GFM.DVOCPump

/-! # dVOC with a DC bus under grid-voltage amplitude modulation

The dVOC core of `DVOCPump` with the port power scaled by the grid-voltage magnitude,
`p(Ψ, V) = (V/V₀) p(Ψ)`. The voltage enters the angle and DC-bus equations (input `B_V`) and three
Jacobian entries (`G_V ≠ 0`); at the normalized Hopf point the voltage input is a multiple of the
angle input, `B_V = −(ν_P/(ν_K V₀)) B_θ`, so the forced response is that multiple of the angle
forced response. The pump is derived exactly; at no load (`P₀ = 0`) the voltage input vanishes but
the direct modulation still pumps, `g_V = −v/(2(ν_δ + j))`.

Model boundary.
* As `DVOCPump`: state `(δ, v_dc, x_I)`, DC source `I_in = P₀`, DC-voltage PI loop, amplitude loop
  eliminated (`E = 1`), quasi-static port power; here `p(Ψ, V) = (V/V₀) p(Ψ)` (`fieldV`), i.e. a
  power proportional to the grid-voltage magnitude (`E = 1` behind a quasi-static link), grid
  angle fixed.
* Normalized Hopf point as in `DVOCPump`: `ν_δ = ηK`, `ν_P = P₀/C`, `ν_K = K/C`, `Ω = 1`,
  `p'' = −τK`; relative amplitude `v = V̂/V₀`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (dVOC core), (25) (angle pump); the voltage excitation is new.

Results.
* `jacV`, `hasFDerivAt_fieldV` — the Jacobian of the voltage-scaled field;
  `hasDerivAt_fieldV_input` — `B_V = −(ηP₀, P₀/C, 0)/V₀`.
* `line_jacV`, `modulationV_eq` — `A₁` along `(z⁽¹⁾, V̂)`: `(δ,δ) = −η(p'' z_δ + K V̂/V₀)`,
  `(v_dc,δ) = −(p'' z_δ + K V̂/V₀)/C + (K/C) z_v`, `(v_dc,v_dc) = (K/C) z_δ + (P₀/C) V̂/V₀ − (2P₀/C) z_v`.
* `voltage_equilibrium` — at `V = V₀`: nominal Jacobian, `B_V = −(ν_P/(ν_K V₀)) B_θ`, normalized
  modulation `hopfModV`; `forcedV_eq` — the voltage forced response `−(v ν_P/ν_K) z⁽¹⁾`.
* `pumpV_eq` — `g_V = −(j v/(6ν_K)) N_V/𝒟` with
  `N_V = ν_K(3ν_P² + ν_P ν_δ + 6 + j(ν_P − 3ν_δ)) − τ ν_P(ν_P + j)(ν_P + 3ν_δ − 2j)` and
  `𝒟 = (ν_i + j)(ν_i + 2j)` of (25); `normalizedPumpV_eq` — `ĝ_V = (|v|/(3|ν_K|)) |N_V|/|𝒟|`.
* `pumpV_noload`, `normalizedPumpV_noload` — `P₀ = 0`: `g_V = −v/(2(ν_δ + j))`,
  `ĝ_V = |v|/√(ν_δ² + 1)`.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the dVOC core (input, modulation, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace DVOCCore
open powerlib.Dynamics (State)
open Complex Matrix

variable (d : DVOCCore)

/-- The Jacobian of the dVOC core when the port power scales with the grid-voltage magnitude,
`p(Ψ, V) = (V/V₀) p(Ψ)`: power `(V/V₀) P`, slope `(V/V₀) K`. -/
def jacV (V0 V P K v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := d.jacobian (V / V0 * P) (V / V0 * K) v

/-- The voltage input `∂f/∂V = −(η P₀, P₀/C, 0)/V₀` at the equilibrium. -/
def inputV (V0 : ℝ) : Fin 3 → ℝ := ![-(d.η * d.P0 / V0), -(d.P0 / (d.C * V0)), 0]

/-- The dVOC core field with the port power scaled by the grid-voltage magnitude,
`p(Ψ, V) = (V/V₀) p(Ψ)` (grid angle `θ`, grid voltage `V`). -/
def fieldV (θ V0 V : ℝ) (x : State 3) : State 3 :=
  ({ d with p := fun Ψ => V / V0 * d.p Ψ } : DVOCCore).field θ x

/-- `∂f/∂x = jacV`: the Jacobian of the voltage-scaled field. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_fieldV {θ V0 V K : ℝ} {x : State 3}
    (hP : HasDerivAt d.p K (x 0 - θ)) (hv : x 1 ≠ 0) :
    HasFDerivAt (d.fieldV θ V0 V)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (d.jacV V0 V (d.p (x 0 - θ)) K (x 1))) x :=
  ({ d with p := fun Ψ => V / V0 * d.p Ψ } : DVOCCore).hasFDerivAt_field
    (hP.const_mul (V / V0)) hv

/-- `∂f/∂V = B_V = inputV` at an equilibrium (`p(Ψ₀) = P₀`, `v_dc = 1`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fieldV_input (θ V0 V : ℝ) (x : State 3)
    (hp : d.p (x 0 - θ) = d.P0) (hx : x 1 = 1) (i : Fin 3) :
    HasDerivAt (fun V => d.fieldV θ V0 V x i) (d.inputV V0 i) V := by
  fin_cases i
  · have h := (((hasDerivAt_id' V).div_const V0).mul_const (d.p (x 0 - θ))).const_sub
      (d.P0 + d.kp * (x 1 - 1) + d.ki * x 2) |>.const_mul d.η
    convert h using 1
    · funext V; simp [fieldV, field]
    · show -(d.η * d.P0 / V0) = _
      rw [hp]; ring
  · have h := ((((hasDerivAt_id' V).div_const V0).mul_const (d.p (x 0 - θ))).div_const
      (x 1)).const_sub d.P0 |>.div_const d.C
    convert h using 1
    · funext V; simp [fieldV, field]
    · show -(d.P0 / (d.C * V0)) = _
      rw [hp, hx]; ring
  · simpa [fieldV, field, inputV] using hasDerivAt_const V (x 1 - 1)

/-- Along `(Ψ, v, V) = (Ψ₀, 1, V₀) + t (z_Ψ, z_v, V̂)` (real direction, linear in it) the three
modulable entries of the Jacobian move with the derivatives
`(δ,δ): −η(p'' z_Ψ + K V̂/V₀)`, `(v,δ): −(p'' z_Ψ + K V̂/V₀)/C + (K/C) z_v`,
`(v,v): (K/C) z_Ψ + (P₀/C) V̂/V₀ − (2P₀/C) z_v`: `G_V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem line_jacV {V0 Ψ0 K P2 zΨ zv zV : ℝ} (hV0 : V0 ≠ 0) (hC : d.C ≠ 0)
    (hP : HasDerivAt d.p K Ψ0) (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (hpe : d.p Ψ0 = d.P0)
    (hK : deriv d.p Ψ0 = K) :
    HasDerivAt (fun t => d.jacV V0 (V0 + t * zV) (d.p (Ψ0 + t * zΨ)) (deriv d.p (Ψ0 + t * zΨ))
        (1 + t * zv) 0 0) (-(d.η * (P2 * zΨ + K * zV / V0))) 0 ∧
      HasDerivAt (fun t => d.jacV V0 (V0 + t * zV) (d.p (Ψ0 + t * zΨ)) (deriv d.p (Ψ0 + t * zΨ))
        (1 + t * zv) 1 0) (-((P2 * zΨ + K * zV / V0) / d.C) + K / d.C * zv) 0 ∧
      HasDerivAt (fun t => d.jacV V0 (V0 + t * zV) (d.p (Ψ0 + t * zΨ)) (deriv d.p (Ψ0 + t * zΨ))
        (1 + t * zv) 1 1) (K / d.C * zΨ + d.P0 / d.C * zV / V0 - 2 * d.P0 / d.C * zv) 0 := by
  have hL : HasDerivAt (fun t : ℝ => Ψ0 + t * zΨ) zΨ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const zΨ).const_add Ψ0
  have hp1 : HasDerivAt (fun t => d.p (Ψ0 + t * zΨ)) (K * zΨ) 0 :=
    HasDerivAt.comp_of_eq 0 hP hL (by simp)
  have hp2 : HasDerivAt (fun t => deriv d.p (Ψ0 + t * zΨ)) (P2 * zΨ) 0 :=
    HasDerivAt.comp_of_eq 0 hP2 hL (by simp)
  have hV : HasDerivAt (fun t : ℝ => (V0 + t * zV) / V0) (zV / V0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const zV).const_add V0).div_const V0
  have hv : HasDerivAt (fun t : ℝ => 1 + t * zv) zv 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const zv).const_add 1
  have hne1 : d.C * (1 + 0 * zv) ≠ 0 := by simpa using hC
  have hne2 : d.C * (1 + 0 * zv) ^ 2 ≠ 0 := by simpa using hC
  refine ⟨?_, ?_, ?_⟩
  · have h := (hV.mul hp2).const_mul (-d.η)
    convert h using 1
    · funext t; simp [jacV, jacobian]
    · simp only [zero_mul, add_zero, hK, div_self hV0]; field_simp; ring
  · have h := ((hV.mul hp2).div (hv.const_mul d.C) hne1).neg
    convert h using 1
    · funext t; simp [jacV, jacobian]
    · simp only [Pi.mul_apply, zero_mul, add_zero, hK, div_self hV0]; field_simp; ring
  · have h := (hV.mul hp1).div ((hv.pow 2).const_mul d.C) hne2
    convert h using 1
    · funext t; simp [jacV, jacobian]
    · simp only [Pi.mul_apply, Pi.pow_apply, zero_mul, add_zero, hpe, div_self hV0]; field_simp; ring

/-! ## The modulation `A₁` under a voltage-magnitude modulation -/

/-- The Jacobian along `(x, V)` at the fixed grid angle `θ`. -/
def jacAtV (θ V0 : ℝ) (q : State 3 × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  d.jacV V0 q.2 (d.p (q.1 0 - θ)) (deriv d.p (q.1 0 - θ)) (q.1 1)

/-- The voltage modulation matrix at the equilibrium (`v_dc = 1`, `p(Ψ₀) = P₀`, `V = V₀`),
`P₂ = p''(Ψ₀)`, along `(z⁽¹⁾, V̂)`. -/
def modMatrixV (V0 K P2 vh : ℝ) (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-(d.η * P2) : ℝ) * z 0 - (d.η * K * vh / V0 : ℝ), 0, 0;
    (-(P2 / d.C) : ℝ) * z 0 - (K * vh / (d.C * V0) : ℝ) + (K / d.C : ℝ) * z 1,
      (K / d.C : ℝ) * z 0 + (d.P0 * vh / (d.C * V0) : ℝ) - (2 * d.P0 / d.C : ℝ) * z 1, 0;
    0, 0, 0]

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_quot {E : Type*}
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

/-- `A₁` of the dVOC core along the forced direction `(z⁽¹⁾, V̂)` (grid angle fixed): the
`(δ,δ)`, `(v_dc,δ)`, `(v_dc,v_dc)` entries acquire the direct voltage terms
`−ηK V̂/V₀`, `−(K/C) V̂/V₀`, `(P₀/C) V̂/V₀` (`G_V ≠ 0`). -/
@[tmio M, powerlib_domain] theorem modulationV_eq {x : State 3} {θ V0 K P2 vh : ℝ}
    (hC : d.C ≠ 0) (hV0 : V0 ≠ 0) (hx1 : x 1 = 1) (hpe : d.p (x 0 - θ) = d.P0)
    (hP : HasDerivAt d.p K (x 0 - θ)) (hP2 : HasDerivAt (deriv d.p) P2 (x 0 - θ))
    (z : Fin 3 → ℂ) :
    ParametricResonance.Element.modulation (d.jacAtV θ V0) (x, V0)
        (WithLp.toLp 2 (fun i => (z i).re), vh) (WithLp.toLp 2 (fun i => (z i).im), 0) =
      d.modMatrixV V0 K P2 vh z := by
  have hK : deriv d.p (x 0 - θ) = K := hP.deriv
  have hL := ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).hasFDerivAt.comp (x, V0)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, V0)))).sub_const θ
  have hv := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt.comp
    (x, V0) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, V0)))
  have hW := (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, V0))).mul_const V0⁻¹
  have hdp := hP2.comp_hasFDerivAt (x, V0) hL
  have hp := hP.comp_hasFDerivAt (x, V0) hL
  have h00 := (hW.mul hdp).const_mul (-d.η)
  have h10 := (hasFDerivAt_quot (hW.mul hdp) (hv.const_mul d.C) (by simpa [hx1] using hC)).neg
  have h11 := hasFDerivAt_quot (hW.mul hp) ((hv.pow 2).const_mul d.C) (by simp [hx1, hC])
  have e00 : HasFDerivAt (fun q : State 3 × ℝ => d.jacAtV θ V0 q 0 0) _ (x, V0) :=
    h00.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
      simp [jacAtV, jacV, jacobian, div_eq_mul_inv])
  have e10 : HasFDerivAt (fun q : State 3 × ℝ => d.jacAtV θ V0 q 1 0) _ (x, V0) :=
    h10.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
      simp [jacAtV, jacV, jacobian, div_eq_mul_inv])
  have e11 : HasFDerivAt (fun q : State 3 × ℝ => d.jacAtV θ V0 q 1 1) _ (x, V0) :=
    h11.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
      simp [jacAtV, jacV, jacobian, div_eq_mul_inv])
  have hz0 := Complex.re_add_im (z 0)
  have hz1 := Complex.re_add_im (z 1)
  have hV0' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
  ext i k
  by_cases hik : (i = 0 ∧ k = 0) ∨ (i = 1 ∧ k = 0) ∨ (i = 1 ∧ k = 1)
  · rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [ParametricResonance.Element.modulation]
      rw [e00.fderiv]
      simp [modMatrixV, hK]
      conv_rhs => rw [← hz0]
      field_simp
      ring
    · simp only [ParametricResonance.Element.modulation]
      rw [e10.fderiv]
      simp [modMatrixV, hx1, hK]
      conv_rhs => rw [← hz0, ← hz1]
      field_simp
      ring
    · simp only [ParametricResonance.Element.modulation]
      rw [e11.fderiv]
      simp [modMatrixV, hx1, hpe]
      conv_rhs => rw [← hz0, ← hz1]
      field_simp
      ring
  · have hc : ∃ c : ℝ, ∀ q, d.jacAtV θ V0 q i k = c := by
      fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> simp [jacAtV, jacV, jacobian]
    obtain ⟨c, hc⟩ := hc
    rw [ParametricResonance.Element.modulation_eq_zero_of_const hc]
    fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> simp [modMatrixV]

/-! ## The normalized Hopf point under a voltage modulation -/

/-- The normalized voltage modulation (`p'' = −τ K`, relative amplitude `v = V̂/V₀`). -/
def hopfModV (νδ νP νK τ v : ℝ) (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(νδ : ℂ) * ((τ : ℂ) * z 0 - v), 0, 0;
    (νK : ℂ) * ((τ : ℂ) * z 0 - v) + (νK : ℂ) * z 1,
      (νK : ℂ) * z 0 + (νP : ℂ) * v - 2 * (νP : ℂ) * z 1, 0; 0, 0, 0]

/-- At `V = V₀` the Jacobian is the nominal one; the voltage input is
`B_V = −(ν_P/(ν_K V₀)) B_θ` (a multiple of the angle input), and the voltage modulation is the
normalized `hopfModV` with relative amplitude `V̂/V₀`. -/
@[tmio M, powerlib_domain] theorem voltage_equilibrium {K τ νδ νP νK V0 vh : ℝ}
    (hδ : d.η * K = νδ) (hP : d.P0 / d.C = νP) (hK : K / d.C = νK) (hνK : νK ≠ 0)
    (hV0 : V0 ≠ 0) (z : Fin 3 → ℂ) :
    d.jacV V0 V0 d.P0 K 1 = d.jacobian d.P0 K 1 ∧
      (fun i => ((d.inputV V0 i : ℝ) : ℂ)) = (-(νP / (νK * V0) : ℝ) : ℂ) • hopfInput νδ νK ∧
      d.modMatrixV V0 K (-(τ * K)) vh z = hopfModV νδ νP νK τ (vh / V0) z := by
  have hC : d.C ≠ 0 := by
    rintro h; apply hνK; rw [← hK, h, div_zero]
  have hK0 : K ≠ 0 := by
    rintro h; apply hνK; rw [← hK, h, zero_div]
  refine ⟨by simp [jacV, div_self hV0], ?_, ?_⟩
  · subst hδ hP hK
    have hV0' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
    have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
    have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK0
    funext i; fin_cases i <;> simp [inputV, hopfInput] <;> field_simp
  · subst hδ hP hK
    have hV0' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
    have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
    ext i k; fin_cases i <;> fin_cases k <;> simp [modMatrixV, hopfModV] <;> field_simp

/-- The forced response to the voltage input `−(v ν_P/ν_K) B_θ` is the same multiple of the
angle forced response: `(2jI − A₀)(c z⁽¹⁾) = c B_θ`. -/
@[tmio M, powerlib_domain] theorem forcedV_eq {νδ νP νK : ℝ} (hνK : νK ≠ 0) (c : ℂ) :
    Linear.characteristicMatrix (hopfMatrix νδ νP νK) (2 * I) *ᵥ (c • forced νδ νP νK) =
      c • hopfInput νδ νK := by
  rw [Matrix.mulVec_smul, forced_eq hνK]

/-- The numerator of the voltage pump,
`N_V = ν_K(3ν_P² + ν_P ν_δ + 6 + j(ν_P − 3ν_δ)) − τ ν_P (ν_P + j)(ν_P + 3ν_δ − 2j)`. -/
def numV (νδ νP νK τ : ℝ) : ℂ :=
  (νK : ℂ) * (3 * (νP : ℂ) ^ 2 + νP * νδ + I * νP - 3 * I * νδ + 6) -
    τ * νP * ((νP : ℂ) + I) * ((νP : ℂ) + 3 * νδ - 2 * I)

@[tmio T, powerlib_foundation] private theorem ne_of_im {x y : ℝ} (hy : y ≠ 0) :
    (x : ℂ) + y * I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hy this

/-- The 2:1 pump coefficient of the dVOC core under a voltage-magnitude modulation of relative
amplitude `v` (normalization `r_{x_I} = 1`): `g_V = −(j v/(6ν_K)) N_V/𝒟`. -/
@[tmio M, powerlib_domain] theorem pumpV_eq {νδ νP νK τ : ℝ} (hνK : νK ≠ 0) (v : ℝ) :
    ParametricResonance.Element.pump
        (hopfModV νδ νP νK τ v ((-(v * νP / νK) : ℝ) • forced νδ νP νK)) (left νδ νP νK)
        (right νP νK) = -(I * v / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) := by
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have h1 : (νP : ℂ) - νδ - I ≠ 0 := by
    have := ne_of_im (x := νP - νδ) (y := -1) (by norm_num); push_cast at this
    simpa [sub_eq_add_neg] using this
  have h2 : (νP : ℂ) - νδ - 2 * I ≠ 0 := by
    have := ne_of_im (x := νP - νδ) (y := -2) (by norm_num); push_cast at this
    simpa [sub_eq_add_neg] using this
  have hA : (νδ : ℂ) - νP + I ≠ 0 := by
    have := ne_of_im (x := νδ - νP) (y := 1) (by norm_num); push_cast at this
    simpa using this
  have hB : (νδ : ℂ) - νP + 2 * I ≠ 0 := by
    have := ne_of_im (x := νδ - νP) (y := 2) (by norm_num); push_cast at this
    simpa using this
  have hB' : (νδ : ℂ) - νP + I * 2 ≠ 0 := by rwa [mul_comm]
  have h2' : (νP : ℂ) - νδ - I * 2 ≠ 0 := by rwa [mul_comm]
  simp [ParametricResonance.Element.pump, hopfModV, forced, left, right, mulVec, dotProduct,
    Fin.sum_univ_three, numV, denD]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- At no load (`P₀ = 0`, `ν_P = 0`) the voltage input vanishes (`B_V = 0`), yet the direct
modulation of `(δ,δ)` and `(v_dc,δ)` still pumps: `g_V = −v/(2(ν_δ + j))`. -/
@[tmio M, powerlib_domain] theorem pumpV_noload {νδ νK τ : ℝ} (hνK : νK ≠ 0) (v : ℝ) :
    ParametricResonance.Element.pump
        (hopfModV νδ 0 νK τ v ((-(v * 0 / νK) : ℝ) • forced νδ 0 νK)) (left νδ 0 νK)
        (right 0 νK) = -(v / (2 * ((νδ : ℂ) + I))) := by
  rw [pumpV_eq hνK]
  have hνK' : (νK : ℂ) ≠ 0 := by exact_mod_cast hνK
  have hA : (νδ : ℂ) + I ≠ 0 := by simpa using ne_of_im (x := νδ) (y := 1) one_ne_zero
  have hB : (νδ : ℂ) + 2 * I ≠ 0 := by simpa using ne_of_im (x := νδ) (y := 2) two_ne_zero
  have hB' : (νδ : ℂ) + I * 2 ≠ 0 := by rwa [mul_comm]
  simp [numV, denD]
  field_simp
  ring_nf
  simp [I_sq]

/-- Normalized voltage pump `ĝ_V = 2|g_V| = (|v|/(3|ν_K|)) |N_V|/|𝒟|`, for every phase
normalization of the eigenvectors. -/
@[tmio M, powerlib_domain] theorem normalizedPumpV_eq {νδ νP νK τ : ℝ} (hνK : νK ≠ 0) (v : ℝ)
    {c : ℂ} (hc : c ≠ 0) :
    ParametricResonance.Element.normalizedPump
        (ParametricResonance.Element.pump
          (hopfModV νδ νP νK τ v ((-(v * νP / νK) : ℝ) • forced νδ νP νK))
          (c⁻¹ • left νδ νP νK) (c • right νP νK)) 1 =
      |v| / (3 * |νK|) * (‖numV νδ νP νK τ‖ / ‖denD νδ νP‖) := by
  rw [ParametricResonance.Element.normalizedPump, ParametricResonance.Element.norm_pump_rescale _ _ _ hc,
    pumpV_eq hνK, norm_mul, norm_neg, norm_div, norm_div, norm_mul, norm_mul]
  simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  rw [show ‖(6 : ℂ)‖ = 6 by simp]
  field_simp
  ring

/-- No load: `ĝ_V = |v|/√(ν_δ² + 1)`, nonzero for `v ≠ 0`. -/
@[tmio M, powerlib_domain] theorem normalizedPumpV_noload {νδ νK τ : ℝ} (hνK : νK ≠ 0) (v : ℝ) :
    ParametricResonance.Element.normalizedPump
        (ParametricResonance.Element.pump
          (hopfModV νδ 0 νK τ v ((-(v * 0 / νK) : ℝ) • forced νδ 0 νK)) (left νδ 0 νK)
          (right 0 νK)) 1 = |v| / Real.sqrt (νδ ^ 2 + 1) := by
  rw [ParametricResonance.Element.normalizedPump, pumpV_noload hνK, norm_neg, norm_div, norm_mul]
  have hn : ‖(νδ : ℂ) + I‖ = Real.sqrt (νδ ^ 2 + 1) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  rw [hn]
  have hs : 0 < Real.sqrt (νδ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
  field_simp

end DVOCCore
end powerlib.GFM
