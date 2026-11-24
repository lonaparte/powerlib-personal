import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.PH.Realizability

/-! # Port-Hamiltonian structure of the GFM VSM with a power filter

Which port-Hamiltonian forms the three-state VSM + power-filter field admits: none with constant
interconnection and dissipation, an explicit one with angle-dependent `J(δ)`, `R(δ)` whose
dissipation is positive semidefinite exactly when `|K₀| ≤ D ω_c`, and a linear one of its
linearization exactly inside the Routh region.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/VSMLPF.lean`: state `x = (δ, ω, P_f)` in this
  order (power angle against the infinite bus, frequency deviation, filtered active power),
  continuous time, `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)`,
  `K₀ = E V_g / X_g` (constant EMF, lossless line), active power export-positive. Excluded as
  there: voltage / reactive loop, inner loops, limits, PLL, delay, PWM, line dynamics.
* Port of the pH form: one input `u`, an additive set-point deviation `P₀ ↦ P₀ + u` entering the
  frequency equation (input matrix `(0, 1/M, 0)ᵀ`), output `y = ω`; `u y` is the power delivered
  to the virtual rotor (incoming-positive, as in `theorem/PH/Nonlinear.lean`). The grid-angle
  input of `VSMLPF.fieldU` is not a port here.
* Parameters: `M ≠ 0` (positive where stated), `D > 0`, `ω_c > 0` (the boundary `D = 0` only in
  `exists_constPH_of_D_eq_zero`), a weight `b > 0` of the filter-error energy; `K₀`, `P₀`
  arbitrary unless stated.
* Level: static structure of the field and of its Jacobian; no stability statement (those are
  the connection statements of `VSMLPF.family`).

Source: GFM port-structure study note (t1-port, §(c) "pH form", items (i)–(iii): derivation and
symbolic checks `c2_ph_vsmlpf.py`); van der Schaft and Jeltsema, *Port-Hamiltonian Systems
Theory: An Introductory Overview* (2014), §2 (input-state-output pH form); work-sync
`theory/T-ph.md` §1.1, §1.10. The generic obligations are `theorem/PH/Realizability.lean`.

Results.
* No constant structure: for `M > 0`, `D ω_c > 0`, `K₀ ≠ 0` no nonlinear pH model with constant
  `J`, `R` (any Hamiltonian, bounded or not, any number of ports) has the VSM + filter field as its
  zero-input field (`not_exists_constPH`): the field's values span `ℝ³`, so `N = J − R` is
  invertible, the Hessian `N⁻¹ Df(x)` is symmetric at `δ = 0` and `δ = π/2`, and with
  `vᵀ N⁻¹ v ≤ 0` the last column of `N⁻¹` vanishes. The damping hypothesis is sharp: at `D = 0`
  (`M > 0`) a constant structure with an indefinite Hamiltonian exists
  (`exists_constPH_of_D_eq_zero`).
* Angle-dependent structure: with `H_b = ½ M ω² − P₀ δ − K₀ cos δ + (b/2)(K₀ sin δ − P_f)²`
  (`phEnergy`, gradient `phGrad`), `κ = (1 + b K₀ cos δ)/(M b)`,
  `J = [[0, 1/M, 0], [−1/M, 0, −κ/2], [0, κ/2, 0]]` (`phJ`),
  `R = [[0, 0, 0], [0, D/M², κ/2], [0, κ/2, ω_c/b]]` (`phR`): `(J − R) ∇H_b = f`
  (`phField_eq`). `R(δ) ⪰ 0 ⇔ (1 + b K₀ cos δ)² ≤ 4 D ω_c b` (`phR_posSemidef_iff`), for all
  states `⇔ (1 + b |K₀|)² ≤ 4 D ω_c b` (`forall_phR_posSemidef_iff`), and some `b > 0` works
  `⇔ |K₀| ≤ D ω_c` (`exists_phR_posSemidef_iff`; `b = 1/(D ω_c)`). Then `phModel` is a
  `PH.NonlinearModel 3 1` with zero-input field the VSM + filter field (`phModel_zeroInputField`),
  field the model at the shifted set point (`phModel_field`) and output `ω` (`phModel_output`).
* Linearization: the Jacobian `J(δ)` (`VSMLPF.jacobian`) is `(J − R) Q` with `J` skew, `R ≻ 0`,
  `Q ≻ 0` iff `0 < K₀ cos δ < D ω_c + D²/M` (`exists_linearPH_jacobian_iff`, the Routh region,
  through `PH.exists_linearPH_posDef_iff`); a form with `R ⪰ 0` forces
  `0 ≤ K₀ cos δ ≤ D ω_c + D²/M` (`linearPH_jacobian_bounds`), and conversely both boundary
  values admit one: a form with `R ⪰ 0` exists iff `0 ≤ K₀ cos δ ≤ D ω_c + D²/M`
  (`exists_linearPH_posSemidef_jacobian_iff`, through `PH.exists_linearPH_posSemidef_iff` with
  explicit Lyapunov matrices at the fold `K₀ cos δ = 0` and the Hopf boundary).
* The two-state swing reduction (no filter) is the library's classical machine
  `Synchronous.classicalSM` (`P_m = P_ref − c₀`, `b = A`, angle `δ − α`) and its linearization
  `Synchronous.SwingParams.linearPH`; they are not restated.

Family and connection conclusions.
* None: static structure. The stability conclusions of the model are the connection statements of
  `VSMLPF.family`; no family reads `phModel`.
-/

noncomputable section
namespace powerlib.GFM
open Matrix
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)

namespace VSMLPF

variable (g : VSMLPF)

/-! ## No constant structure -/

/-- The algebra of the refutation: a matrix `G` whose products with the Jacobians at `δ = 0` and
`δ = π/2` are symmetric and whose quadratic form is nonpositive has a vanishing last column. -/
@[tmio M, powerlib_domain] private theorem constPH_column (hM : 0 < g.M) (hDω : 0 < g.D * g.ωc)
    (hωK : g.ωc * g.K0 ≠ 0) {G : Matrix (Fin 3) (Fin 3) ℝ}
    (h0 : (G * g.jacobian 0)ᵀ = G * g.jacobian 0)
    (h1 : (G * g.jacobian (Real.pi / 2))ᵀ = G * g.jacobian (Real.pi / 2))
    (hN : ∀ v, v ⬝ᵥ (G *ᵥ v) ≤ 0) : G 0 2 = 0 ∧ G 1 2 = 0 ∧ G 2 2 = 0 := by
  have hM' : g.M ≠ 0 := hM.ne'
  have ent : ∀ (δ : ℝ) (i j : Fin 3), (G * g.jacobian δ) i j =
      G i 2 * (g.ωc * (g.K0 * Real.cos δ)) * (if j = 0 then 1 else 0) +
        (G i 0 - g.D / g.M * G i 1) * (if j = 1 then 1 else 0) +
        (-(G i 1) / g.M - g.ωc * G i 2) * (if j = 2 then 1 else 0) := by
    intro δ i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, jacobian] <;> ring
  have sym : ∀ δ, (G * g.jacobian δ)ᵀ = G * g.jacobian δ → ∀ i j : Fin 3,
      (G * g.jacobian δ) j i = (G * g.jacobian δ) i j := fun δ h i j => by
    simpa using congrFun (congrFun h i) j
  have a01 := sym 0 h0 0 1
  have b01 := sym _ h1 0 1
  have a02 := sym 0 h0 0 2
  have b02 := sym _ h1 0 2
  have a12 := sym 0 h0 1 2
  simp only [ent, Real.cos_zero, Real.cos_pi_div_two] at a01 b01 a02 b02 a12
  norm_num at a01 b01 a02 b02 a12
  have g12 : G 1 2 = 0 := by
    have : G 1 2 * (g.ωc * g.K0) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hωK
  have g22 : G 2 2 = 0 := by
    have : G 2 2 * (g.ωc * g.K0) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hωK
  have quad : ∀ v : Fin 3 → ℝ, v ⬝ᵥ (G *ᵥ v) = ∑ i, ∑ j, v i * G i j * v j := fun v => by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- An affine function `a + b t ≤ 0` for every `t` has slope `b = 0`.
  have slope : ∀ a b : ℝ, (∀ t : ℝ, a + b * t ≤ 0) → b = 0 := fun a b h => by
    have hd := discrim_le_zero (a := (0 : ℝ)) (b := -b) (c := -a) fun t => by
      linarith [h t]
    rw [discrim] at hd
    nlinarith [sq_nonneg b]
  -- The quadratic form along `e_k + t e₂` is affine in `t` (`G 2 2 = 0`).
  have s0 : G 0 2 + G 2 0 = 0 := slope (G 0 0) _ fun t => by
    have h := hN ![1, 0, t]
    rw [quad] at h
    simp [Fin.sum_univ_three, g22] at h
    linarith
  have s1 : G 1 2 + G 2 1 = 0 := slope (G 1 1) _ fun t => by
    have h := hN ![0, 1, t]
    rw [quad] at h
    simp [Fin.sum_univ_three, g22] at h
    linarith
  have d0 := hN ![1, 0, 0]
  have d1 := hN ![0, 1, 0]
  rw [quad] at d0 d1
  simp [Fin.sum_univ_three] at d0 d1
  -- `G₀₀ = −D ω_c G₀₂` and `G₁₁ = M G₀₂`, of opposite signs.
  have e01 : G 0 1 = -(g.M * g.ωc) * G 0 2 := by
    have h : G 0 1 / g.M = -(g.ωc * G 0 2) := by rw [neg_div] at b02; linarith
    rw [div_eq_iff hM'] at h
    linarith
  have e00 : G 0 0 = -(g.D * g.ωc) * G 0 2 := by
    have h : g.D / g.M * (-(g.M * g.ωc) * G 0 2) = -(g.D * g.ωc) * G 0 2 := by
      field_simp
    rw [e01] at b01
    linarith
  have e11 : G 1 1 = g.M * G 0 2 := by
    have h21 : G 2 1 = 0 := by linarith
    rw [g12, h21, mul_zero, mul_zero, sub_zero, sub_zero, neg_div] at a12
    have h : G 1 1 / g.M = G 0 2 := by linarith
    rw [div_eq_iff hM'] at h
    linarith
  have c0 : G 0 2 = 0 := by
    rw [e00] at d0
    rw [e11] at d1
    have h1' : 0 ≤ G 0 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    have h2' : G 0 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  exact ⟨c0, g12, g22⟩

/-- **No constant port-Hamiltonian structure.** For `M > 0`, `D ω_c > 0` and `K₀ ≠ 0`, no
nonlinear pH model with constant interconnection `J` and dissipation `R` — whatever its
Hamiltonian (bounded below or not) and its ports — has the VSM + power-filter field as its
zero-input field. Static structure of the model's field. -/
@[tmio M, powerlib_domain] theorem not_exists_constPH (hM : 0 < g.M) (hDω : 0 < g.D * g.ωc)
    (hK0 : g.K0 ≠ 0) {m : ℕ} :
    ¬ ∃ P : PH.NonlinearModel 3 m, (∀ x, P.J x = P.J 0) ∧ (∀ x, P.R x = P.R 0) ∧
      P.zeroInputField = g.field := by
  rintro ⟨P, hJ, hR, hf⟩
  have hM' : g.M ≠ 0 := hM.ne'
  have hωc : g.ωc ≠ 0 := fun h => by rw [h, mul_zero] at hDω; exact lt_irrefl _ hDω
  have hωK : g.ωc * g.K0 ≠ 0 := mul_ne_zero hωc hK0
  -- The values of the field span `ℝ³`, so `N = J − R` is invertible.
  have hdet : IsUnit (P.J 0 - P.R 0).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨a, ha, hfa⟩ := P.exists_covector_of_det_eq_zero hJ hR h0
    rw [hf] at hfa
    have ev : ∀ x : State 3, a 0 * x 1 + a 1 * ((g.P0 - x 2 - g.D * x 1) / g.M) +
        a 2 * (g.ωc * (g.K0 * Real.sin (x 0) - x 2)) = 0 := fun x => by
      rw [← hfa x]; simp [dotProduct, Fin.sum_univ_three]
    have e0 := ev (mk3 0 0 0)
    have e1 := ev (mk3 0 1 0)
    have e2 := ev (mk3 0 0 1)
    have e3 := ev (mk3 (Real.pi / 2) 0 0)
    simp only [mk3_zero, mk3_one, mk3_two, Real.sin_zero, Real.sin_pi_div_two] at e0 e1 e2 e3
    have a2 : a 2 = 0 := by
      have h : a 2 * (g.ωc * g.K0) = 0 := by linear_combination e3 - e0
      exact (mul_eq_zero.mp h).resolve_right hωK
    have a1 : a 1 = 0 := by
      have h : a 1 * g.M⁻¹ = 0 := by linear_combination e0 - e2 - g.ωc * a2
      exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero hM')
    have a0 : a 0 = 0 := by linear_combination e1 - e0 + g.D / g.M * a1
    exact ha (funext fun i => by fin_cases i <;> simp [a0, a1, a2])
  have hA : ∀ δ, HasFDerivAt P.zeroInputField
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian δ)) (mk3 δ 0 0) := fun δ => by
    rw [hf]
    simpa using g.hasFDerivAt_field (mk3 δ 0 0)
  obtain ⟨c0, c1, c2⟩ := g.constPH_column hM hDω hωK
    (P.constStructure_hessian_symm hJ hR hdet (hA 0))
    (P.constStructure_hessian_symm hJ hR hdet (hA (Real.pi / 2)))
    (P.constStructure_inv_nonpos hJ hR hdet)
  -- The last column of `N⁻¹` vanishes, contradicting `N N⁻¹ = 1`.
  have hcol : (P.J 0 - P.R 0)⁻¹ *ᵥ Pi.single 2 1 = 0 := by
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [c0, c1, c2]
  have h := congrFun (congrArg (· *ᵥ Pi.single (2 : Fin 3) (1 : ℝ))
    (Matrix.mul_nonsing_inv _ hdet)) 2
  simp only [← mulVec_mulVec, hcol, mulVec_zero, one_mulVec] at h
  simp at h

/-- **The damping hypothesis is sharp.** Without damping (`D = 0`, `M > 0`) the field has a
constant structure: `J = [[0, 0, 1], [0, 0, 0], [−1, 0, 0]]`,
`R = [[0, 0, 0], [0, 1/M, ω_c], [0, ω_c, M ω_c²]] ⪰ 0` and the indefinite Hamiltonian
`H = ω_c (P₀ δ + K₀ cos δ) − M ω_c ω²/2 − P₀ ω + P_f ω`. Static structure of the model's field. -/
@[tmio M, powerlib_domain] theorem exists_constPH_of_D_eq_zero (hD : g.D = 0) (hM : 0 < g.M) :
    ∃ P : PH.NonlinearModel 3 0, (∀ x, P.J x = P.J 0) ∧ (∀ x, P.R x = P.R 0) ∧
      P.zeroInputField = g.field := by
  have hM' : g.M ≠ 0 := hM.ne'
  let H : State 3 → ℝ := fun x => g.ωc * (g.P0 * x 0 + g.K0 * Real.cos (x 0)) -
    g.M * g.ωc * x 1 ^ 2 / 2 - g.P0 * x 1 + x 2 * x 1
  let dH : State 3 → State 3 := fun x => mk3 (g.ωc * (g.P0 - g.K0 * Real.sin (x 0)))
    (-(g.M * g.ωc * x 1) - g.P0 + x 2) (x 1)
  have hgrad : ∀ x, HasGradientAt H (dH x) x := fun x => by
    have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) :
      State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
    have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) :
      State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
    have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) :
      State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
    have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
    have h := ((((h0.const_mul g.P0).add (hc.const_mul g.K0)).const_mul g.ωc).sub
      ((h1.mul h1).const_mul (g.M * g.ωc / 2))).sub (h1.const_mul g.P0) |>.add (h2.mul h1)
    refine PH.hasGradientAt_of_hasFDerivAt (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)) fun v => ?_
    · simp only [H]
      simp
      ring
    · simp [dH, dotProduct, Fin.sum_univ_three]
      ring
  refine ⟨{ J := fun _ => !![0, 0, 1; 0, 0, 0; -1, 0, 0]
            R := fun _ => !![0, 0, 0; 0, 1 / g.M, g.ωc; 0, g.ωc, g.M * g.ωc ^ 2]
            g := fun _ => 0
            H := H
            dH := dH
            skew := fun _ => by ext i j; fin_cases i <;> fin_cases j <;> simp
            dissipation_posSemidef := fun _ => ?_
            hasGradient := hgrad }, fun _ => rfl, fun _ => rfl, ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · have e : star v ⬝ᵥ (!![0, 0, 0; 0, 1 / g.M, g.ωc; 0, g.ωc, g.M * g.ωc ^ 2] *ᵥ v) =
          (v 1 + g.M * g.ωc * v 2) ^ 2 / g.M := by
        simp [dotProduct, mulVec, Fin.sum_univ_three]
        field_simp
      rw [e]
      positivity
  · funext x
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;>
      simp [PH.NonlinearModel.zeroInputField, PH.NonlinearModel.field, dH, field, hD,
        dotProduct, Fin.sum_univ_three]
    · field_simp
      ring
    · ring

/-! ## Angle-dependent structure -/

/-- The energy `H_b(δ, ω, P_f) = ½ M ω² − P₀ δ − K₀ cos δ + (b/2)(K₀ sin δ − P_f)²`. -/
def phEnergy (b : ℝ) (x : State 3) : ℝ :=
  g.M * x 1 ^ 2 / 2 - g.P0 * x 0 - g.K0 * Real.cos (x 0) +
    b / 2 * (g.K0 * Real.sin (x 0) - x 2) ^ 2

/-- The gradient `∇H_b = (K₀ sin δ − P₀ + b e K₀ cos δ, M ω, −b e)`, `e = K₀ sin δ − P_f`. -/
def phGrad (b : ℝ) (x : State 3) : State 3 :=
  mk3 (g.K0 * Real.sin (x 0) - g.P0 +
      b * (g.K0 * Real.sin (x 0) - x 2) * (g.K0 * Real.cos (x 0)))
    (g.M * x 1) (-(b * (g.K0 * Real.sin (x 0) - x 2)))

/-- The coupling `κ(δ) = (1 + b K₀ cos δ)/(M b)`. -/
def phCoupling (b : ℝ) (x : State 3) : ℝ := (1 + b * g.K0 * Real.cos (x 0)) / (g.M * b)

/-- The interconnection `J(δ) = [[0, 1/M, 0], [−1/M, 0, −κ/2], [0, κ/2, 0]]`. -/
def phJ (b : ℝ) (x : State 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1 / g.M, 0; -(1 / g.M), 0, -(g.phCoupling b x / 2); 0, g.phCoupling b x / 2, 0]

/-- The dissipation `R(δ) = [[0, 0, 0], [0, D/M², κ/2], [0, κ/2, ω_c/b]]`. -/
def phR (b : ℝ) (x : State 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, g.D / g.M ^ 2, g.phCoupling b x / 2; 0, g.phCoupling b x / 2, g.ωc / b]

@[tmio M, powerlib_domain] theorem hasGradientAt_phEnergy (b : ℝ) (x : State 3) :
    HasGradientAt (g.phEnergy b) (g.phGrad b x) x := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have he := (hs.const_mul g.K0).sub h2
  have h := ((((h1.mul h1).const_mul (g.M / 2)).sub (h0.const_mul g.P0)).sub
    (hc.const_mul g.K0)).add ((he.mul he).const_mul (b / 2))
  refine PH.hasGradientAt_of_hasFDerivAt (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)) fun v => ?_
  · simp [phEnergy]
    ring
  · simp [phGrad, dotProduct, Fin.sum_univ_three]
    ring

@[tmio M, powerlib_domain] theorem phJ_skew (b : ℝ) (x : State 3) :
    (g.phJ b x)ᵀ = -g.phJ b x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phJ]

/-- `(J(δ) − R(δ)) ∇H_b = f` for `M ≠ 0`, `b ≠ 0`. -/
@[tmio M, powerlib_domain] theorem phField_eq (hM : g.M ≠ 0) {b : ℝ} (hb : b ≠ 0) (x : State 3) :
    (g.phJ b x - g.phR b x) *ᵥ WithLp.ofLp (g.phGrad b x) = WithLp.ofLp (g.field x) := by
  funext i
  fin_cases i
  · simp [phJ, phR, phGrad, phCoupling, field, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
  · simp [phJ, phR, phGrad, phCoupling, field, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  · simp [phJ, phR, phGrad, phCoupling, field, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp

/-- `R(δ) ⪰ 0 ⇔ (1 + b K₀ cos δ)² ≤ 4 D ω_c b` (`M ≠ 0`, `D > 0`, `b > 0`). -/
@[tmio M, powerlib_domain] theorem phR_posSemidef_iff (hM : g.M ≠ 0) (hD : 0 < g.D) {b : ℝ}
    (hb : 0 < b) (x : State 3) :
    (g.phR b x).PosSemidef ↔ (1 + b * g.K0 * Real.cos (x 0)) ^ 2 ≤ 4 * g.D * g.ωc * b := by
  set c := 1 + b * g.K0 * Real.cos (x 0) with hc
  have hκ : g.phCoupling b x = c / (g.M * b) := rfl
  have hM2 : 0 < g.M ^ 2 := by positivity
  have hsymm : (g.phR b x).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phR]
  have hq : ∀ v : Fin 3 → ℝ, star v ⬝ᵥ (g.phR b x *ᵥ v) =
      g.D / g.M ^ 2 * v 1 ^ 2 + 2 * (c / (g.M * b) / 2) * v 1 * v 2 + g.ωc / b * v 2 ^ 2 := by
    intro v
    simp [phR, hκ, dotProduct, mulVec, Fin.sum_univ_three]
    ring
  have key : ∀ v1 v2 : ℝ, 4 * g.M ^ 2 * b ^ 2 *
      (g.D / g.M ^ 2 * v1 ^ 2 + 2 * (c / (g.M * b) / 2) * v1 * v2 + g.ωc / b * v2 ^ 2) =
      4 * b ^ 2 * g.D * v1 ^ 2 + 4 * g.M * b * c * v1 * v2 + 4 * g.M ^ 2 * b * g.ωc * v2 ^ 2 := by
    intro v1 v2
    field_simp
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩
    have hv := h ![0, g.M * c, -(2 * b * g.D)]
    rw [hq] at hv
    have hk := key (g.M * c) (-(2 * b * g.D))
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.tail_cons] at hv
    have hpos : 0 < 4 * g.M ^ 2 * b ^ 2 := by positivity
    have h' := mul_nonneg hpos.le hv
    rw [hk] at h'
    have e : 4 * b ^ 2 * g.D * (g.M * c) ^ 2 + 4 * g.M * b * c * (g.M * c) * -(2 * b * g.D) +
        4 * g.M ^ 2 * b * g.ωc * (-(2 * b * g.D)) ^ 2 =
        4 * g.M ^ 2 * b ^ 2 * g.D * (4 * g.D * g.ωc * b - c ^ 2) := by ring
    rw [e] at h'
    have hp2 : 0 < 4 * g.M ^ 2 * b ^ 2 * g.D := by positivity
    nlinarith
  · intro h
    refine ⟨hsymm, fun v => ?_⟩
    rw [hq]
    have hk := key (v 1) (v 2)
    have hpos : 0 < 4 * g.M ^ 2 * b ^ 2 := by positivity
    have hD' : 0 < 4 * b ^ 2 * g.D := by positivity
    have hsq : 0 ≤ 4 * b ^ 2 * g.D * (4 * b ^ 2 * g.D * v 1 ^ 2 + 4 * g.M * b * c * v 1 * v 2 +
        4 * g.M ^ 2 * b * g.ωc * v 2 ^ 2) := by
      have e : 4 * b ^ 2 * g.D * (4 * b ^ 2 * g.D * v 1 ^ 2 + 4 * g.M * b * c * v 1 * v 2 +
          4 * g.M ^ 2 * b * g.ωc * v 2 ^ 2) =
          (4 * b ^ 2 * g.D * v 1 + 2 * g.M * b * c * v 2) ^ 2 +
            4 * g.M ^ 2 * b ^ 2 * (4 * g.D * g.ωc * b - c ^ 2) * v 2 ^ 2 := by ring
      rw [e]
      have : 0 ≤ 4 * g.M ^ 2 * b ^ 2 * (4 * g.D * g.ωc * b - c ^ 2) * v 2 ^ 2 := by
        have : 0 ≤ 4 * g.D * g.ωc * b - c ^ 2 := by linarith
        positivity
      positivity
    have h3 := (mul_nonneg_iff_of_pos_left hD').mp hsq
    rw [← hk] at h3
    exact (mul_nonneg_iff_of_pos_left hpos).mp h3

/-- `R(δ) ⪰ 0` at every state `⇔ (1 + b |K₀|)² ≤ 4 D ω_c b`. -/
@[tmio M, powerlib_domain] theorem forall_phR_posSemidef_iff (hM : g.M ≠ 0) (hD : 0 < g.D)
    {b : ℝ} (hb : 0 < b) :
    (∀ x, (g.phR b x).PosSemidef) ↔ (1 + b * |g.K0|) ^ 2 ≤ 4 * g.D * g.ωc * b := by
  simp only [g.phR_posSemidef_iff hM hD hb]
  constructor
  · intro h
    rcases le_or_gt 0 g.K0 with hK | hK
    · simpa [abs_of_nonneg hK] using h (mk3 0 0 0)
    · simpa [abs_of_neg hK, mul_neg] using h (mk3 Real.pi 0 0)
  · intro h x
    have hcos := Real.abs_cos_le_one (x 0)
    have hbd : |b * g.K0 * Real.cos (x 0)| ≤ b * |g.K0| := by
      rw [abs_mul, abs_mul, abs_of_pos hb]
      exact mul_le_of_le_one_right (by positivity) hcos
    have h1 := abs_le.mp hbd
    refine le_trans ?_ h
    nlinarith [abs_nonneg g.K0]

/-- **Existence of the angle-dependent structure.** Some weight `b > 0` makes `R(δ) ⪰ 0` at every
state iff `|K₀| ≤ D ω_c` (for `K₀ > 0`: `D ω_c ≥ K₀`); `b = 1/(D ω_c)` works. -/
@[tmio M, powerlib_domain] theorem exists_phR_posSemidef_iff (hM : g.M ≠ 0) (hD : 0 < g.D)
    (hωc : 0 < g.ωc) :
    (∃ b, 0 < b ∧ ∀ x, (g.phR b x).PosSemidef) ↔ |g.K0| ≤ g.D * g.ωc := by
  have hDω : 0 < g.D * g.ωc := mul_pos hD hωc
  constructor
  · rintro ⟨b, hb, h⟩
    have h' := (g.forall_phR_posSemidef_iff hM hD hb).mp h
    have : 4 * b * |g.K0| ≤ 4 * b * (g.D * g.ωc) := by nlinarith [sq_nonneg (1 - b * |g.K0|)]
    nlinarith
  · intro h
    refine ⟨1 / (g.D * g.ωc), by positivity,
      (g.forall_phR_posSemidef_iff hM hD (by positivity)).mpr ?_⟩
    have hr : 1 / (g.D * g.ωc) * |g.K0| ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hDω]
      exact h
    have hr0 : 0 ≤ 1 / (g.D * g.ωc) * |g.K0| := by positivity
    have e : 4 * g.D * g.ωc * (1 / (g.D * g.ωc)) = 4 := by field_simp
    rw [e]
    nlinarith

/-- The VSM + power filter as a nonlinear pH model with the angle-dependent structure, the
energy `H_b` and the set-point port (input matrix `(0, 1/M, 0)ᵀ`), given `R(δ) ⪰ 0` at every
state (`exists_phR_posSemidef_iff`). -/
def phModel (b : ℝ) (hR : ∀ x, (g.phR b x).PosSemidef) : PH.NonlinearModel 3 1 where
  J := g.phJ b
  R := g.phR b
  g _ := !![0; 1 / g.M; 0]
  H := g.phEnergy b
  dH := g.phGrad b
  skew := g.phJ_skew b
  dissipation_posSemidef := hR
  hasGradient := g.hasGradientAt_phEnergy b

/-- With input `u` the pH model is the VSM + filter field at the set point `P₀ + u`. -/
@[tmio M, powerlib_domain] theorem phModel_field (hM : g.M ≠ 0) {b : ℝ} (hb : b ≠ 0)
    (hR : ∀ x, (g.phR b x).PosSemidef) (x : State 3) (u : Fin 1 → ℝ) :
    (g.phModel b hR).field x u = ({ g with P0 := g.P0 + u 0 } : VSMLPF).field x := by
  apply WithLp.ofLp_injective
  rw [PH.NonlinearModel.ofLp_field]
  change (g.phJ b x - g.phR b x) *ᵥ WithLp.ofLp (g.phGrad b x) + !![0; 1 / g.M; 0] *ᵥ u = _
  rw [g.phField_eq hM hb x]
  funext i
  fin_cases i
  · simp [field, dotProduct]
  · simp [field, dotProduct]
    field_simp
    ring
  · simp [field, dotProduct]

/-- The zero-input field of the pH model is the VSM + power-filter field. -/
@[tmio M, powerlib_domain] theorem phModel_zeroInputField (hM : g.M ≠ 0) {b : ℝ} (hb : b ≠ 0)
    (hR : ∀ x, (g.phR b x).PosSemidef) : (g.phModel b hR).zeroInputField = g.field := by
  funext x
  rw [PH.NonlinearModel.zeroInputField, g.phModel_field hM hb hR x 0]
  simp

/-- The collocated output of the set-point port is the frequency deviation `ω`. -/
@[tmio M, powerlib_domain] theorem phModel_output (hM : g.M ≠ 0) {b : ℝ}
    (hR : ∀ x, (g.phR b x).PosSemidef) (x : State 3) :
    (g.phModel b hR).output x = ![x 1] := by
  funext i
  fin_cases i
  simp [PH.NonlinearModel.output, phModel, phGrad, mulVec, dotProduct, Fin.sum_univ_three]
  field_simp

/-! ## Linear pH form of the linearization -/

/-- **Linear pH form iff Routh.** For positive `M, D, ω_c`, the Jacobian at angle `δ` is
`(J − R) Q` with `J` skew, `R ≻ 0`, `Q ≻ 0` iff `0 < K₀ cos δ < D ω_c + D²/M` (the Hurwitz
region, `PH.exists_linearPH_posDef_iff` with `Criteria.isHurwitz_fin_three_iff`). -/
@[tmio M, powerlib_domain] theorem exists_linearPH_jacobian_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hωc : 0 < g.ωc) (δ : ℝ) :
    (∃ J R Q : Matrix (Fin 3) (Fin 3) ℝ, Jᵀ = -J ∧ R.PosDef ∧ Q.PosDef ∧
      PH.linearStateMatrix J R Q = g.jacobian δ) ↔
      0 < g.K0 * Real.cos δ ∧ g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M := by
  rw [PH.exists_linearPH_posDef_iff, Criteria.isHurwitz_fin_three_iff, trace_jacobian,
    det_jacobian, principalMinorSum_jacobian]
  set k := g.K0 * Real.cos δ
  have hgap : (-g.D / g.M - g.ωc) * (g.D * g.ωc / g.M) - -(g.ωc * k) / g.M =
      g.ωc / g.M * (k - (g.D * g.ωc + g.D ^ 2 / g.M)) := by field_simp; ring
  have hdet : -(g.ωc * k) / g.M = -(g.ωc / g.M * k) := by ring
  have hr : 0 < g.ωc / g.M := div_pos hωc hM
  have htr : -g.D / g.M - g.ωc < 0 := by
    have : 0 < g.D / g.M := div_pos hD hM
    rw [neg_div]; linarith
  constructor
  · rintro ⟨-, h2, h3⟩
    rw [hdet, neg_lt_zero] at h2
    refine ⟨pos_of_mul_pos_right h2 hr.le, ?_⟩
    have : g.ωc / g.M * (k - (g.D * g.ωc + g.D ^ 2 / g.M)) < 0 := by linarith
    linarith [(mul_neg_iff.mp this).resolve_right (fun h => absurd h.1 (not_lt.mpr hr.le))]
  · rintro ⟨h1, h2⟩
    refine ⟨htr, by rw [hdet, neg_lt_zero]; exact mul_pos hr h1, ?_⟩
    have : g.ωc / g.M * (k - (g.D * g.ωc + g.D ^ 2 / g.M)) < 0 :=
      mul_neg_of_pos_of_neg hr (by linarith)
    linarith

/-- With only `R ⪰ 0`, a linear pH form `(J − R) Q = J(δ)` (`J` skew, `Q ≻ 0`) forces the closed
Routh region `0 ≤ K₀ cos δ ≤ D ω_c + D²/M`: outside it the characteristic polynomial has a root
with positive real part (`Criteria.exists_cubic_root_re_pos_of_violation`), which no pH state
matrix has (`PH.phSpectral_det_ne_zero`). -/
@[tmio M, powerlib_domain] theorem linearPH_jacobian_bounds (hM : 0 < g.M) (hωc : 0 < g.ωc)
    {δ : ℝ}
    (h : ∃ J R Q : Matrix (Fin 3) (Fin 3) ℝ, Jᵀ = -J ∧ R.PosSemidef ∧ Q.PosDef ∧
      PH.linearStateMatrix J R Q = g.jacobian δ) :
    0 ≤ g.K0 * Real.cos δ ∧ g.K0 * Real.cos δ ≤ g.D * g.ωc + g.D ^ 2 / g.M := by
  obtain ⟨J, R, Q, hJ, hR, hQ, hA⟩ := h
  set k := g.K0 * Real.cos δ
  have hr : 0 < g.ωc / g.M := div_pos hωc hM
  by_contra hk
  have hviol : (-(g.jacobian δ).trace) < 0 ∨ Criteria.principalMinorSum (g.jacobian δ) < 0 ∨
      (-(g.jacobian δ).det) < 0 ∨
      (-(g.jacobian δ).trace) * Criteria.principalMinorSum (g.jacobian δ) <
        -(g.jacobian δ).det := by
    rw [trace_jacobian, det_jacobian, principalMinorSum_jacobian]
    rcases not_and_or.mp hk with h0 | h1
    · right; right; left
      have : g.ωc / g.M * k < 0 := mul_neg_of_pos_of_neg hr (lt_of_not_ge h0)
      have e : -(-(g.ωc * k) / g.M) = g.ωc / g.M * k := by ring
      rw [e]; exact this
    · right; right; right
      have : 0 < g.ωc / g.M * (k - (g.D * g.ωc + g.D ^ 2 / g.M)) :=
        mul_pos hr (by linarith [lt_of_not_ge h1])
      have e : -(-(g.ωc * k) / g.M) - -(-g.D / g.M - g.ωc) * (g.D * g.ωc / g.M) =
          g.ωc / g.M * (k - (g.D * g.ωc + g.D ^ 2 / g.M)) := by field_simp; ring
      linarith
  obtain ⟨s, hs, hre⟩ := Criteria.exists_cubic_root_re_pos_of_violation hviol
  have hdet := PH.phSpectral_det_ne_zero hJ hR hQ hre
  rw [hA, Criteria.det_characteristicMatrix_fin_three'] at hdet
  exact hdet hs

/-- At the fold boundary `K₀ cos δ = 0` the Jacobian has the Lyapunov matrix of
`V = (D ω_c x₀ + M ω_c x₁ − x₂)² + M D ω_c x₁² + x₂²` (the first square is the conserved
combination): `−(Aᵀ Q + Q A) = 2 ω_c [[0, 0, 0], [0, D², D/2], [0, D/2, 1]] ⪰ 0`. -/
@[tmio M, powerlib_domain] private theorem lyapunov_jacobian_of_eq_zero (hM : 0 < g.M)
    (hD : 0 < g.D) (hωc : 0 < g.ωc) {δ : ℝ} (hk : g.K0 * Real.cos δ = 0) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, Q.PosDef ∧
      (-((g.jacobian δ)ᵀ * Q + Q * g.jacobian δ)).PosSemidef := by
  have hM' : g.M ≠ 0 := hM.ne'
  set Q : Matrix (Fin 3) (Fin 3) ℝ :=
    !![g.D ^ 2 * g.ωc ^ 2, g.D * g.M * g.ωc ^ 2, -(g.D * g.ωc);
      g.D * g.M * g.ωc ^ 2, g.M ^ 2 * g.ωc ^ 2 + g.M * g.D * g.ωc, -(g.M * g.ωc);
      -(g.D * g.ωc), -(g.M * g.ωc), 2] with hQ
  have hS : -((g.jacobian δ)ᵀ * Q + Q * g.jacobian δ) =
      !![0, 0, 0; 0, 2 * g.ωc * g.D ^ 2, g.ωc * g.D; 0, g.ωc * g.D, 2 * g.ωc] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hQ, jacobian, Matrix.mul_apply, Fin.sum_univ_three, hk] <;> field_simp <;> ring
  refine ⟨Q, Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ]
  · simp only [star_trivial]
    have e : x ⬝ᵥ (Q *ᵥ x) = (g.D * g.ωc * x 0 + g.M * g.ωc * x 1 - x 2) ^ 2 +
        g.M * g.D * g.ωc * x 1 ^ 2 + x 2 ^ 2 := by
      simp [hQ, dotProduct, mulVec, Fin.sum_univ_three]; ring
    rw [e]
    by_contra hle
    have h1 : 0 ≤ (g.D * g.ωc * x 0 + g.M * g.ωc * x 1 - x 2) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ g.M * g.D * g.ωc * x 1 ^ 2 := by positivity
    have h3 : 0 ≤ x 2 ^ 2 := sq_nonneg _
    have hx2 : x 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have hx1 : x 1 = 0 := by
      have : g.M * g.D * g.ωc * x 1 ^ 2 = 0 := by linarith
      have hc : g.M * g.D * g.ωc ≠ 0 := by positivity
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp this).resolve_left hc)
    have hx0 : x 0 = 0 := by
      have h0 : (g.D * g.ωc * x 0 + g.M * g.ωc * x 1 - x 2) ^ 2 = 0 := by linarith
      rw [hx1, hx2, pow_eq_zero_iff (by norm_num)] at h0
      have hc : g.D * g.ωc ≠ 0 := by positivity
      simpa [hc] using h0
    exact hx (funext fun i => by fin_cases i <;> simp [hx0, hx1, hx2])
  · rw [hS]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · simp only [star_trivial]
      have e : x ⬝ᵥ (!![0, 0, 0; 0, 2 * g.ωc * g.D ^ 2, g.ωc * g.D; 0, g.ωc * g.D, 2 * g.ωc] *ᵥ
          x) = 2 * g.ωc * ((g.D * x 1 + x 2 / 2) ^ 2 + 3 / 4 * x 2 ^ 2) := by
        simp [dotProduct, mulVec, Fin.sum_univ_three]; ring
      rw [e]
      positivity

/-- At the Hopf boundary `K₀ cos δ = D ω_c + D²/M` the Jacobian has the Lyapunov matrix
`Q = M ℓ_r ℓ_rᵀ + D ω_c ℓ_i ℓ_iᵀ + M ℓ₃ ℓ₃ᵀ` built from the left eigenvectors
(`ℓ_r = (0, −M ω_c, 1)`, `ℓ_i = (D + M ω_c, M, 0)` span the undamped pair `±j√(D ω_c/M)`,
`ℓ₃ = (−D ω_c, D, 1)` the real root `−(D/M + ω_c)`):
`−(Aᵀ Q + Q A) = 2 (D + M ω_c) ℓ₃ ℓ₃ᵀ ⪰ 0`. -/
@[tmio M, powerlib_domain] private theorem lyapunov_jacobian_of_eq_routh (hM : 0 < g.M)
    (hD : 0 < g.D) (hωc : 0 < g.ωc) {δ : ℝ}
    (hk : g.K0 * Real.cos δ = g.D * g.ωc + g.D ^ 2 / g.M) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, Q.PosDef ∧
      (-((g.jacobian δ)ᵀ * Q + Q * g.jacobian δ)).PosSemidef := by
  have hM' : g.M ≠ 0 := hM.ne'
  set Q : Matrix (Fin 3) (Fin 3) ℝ :=
    !![g.D ^ 3 * g.ωc + 3 * g.D ^ 2 * g.M * g.ωc ^ 2 + g.D * g.M ^ 2 * g.ωc ^ 3,
        g.D * g.M ^ 2 * g.ωc ^ 2, -(g.D * g.M * g.ωc);
      g.D * g.M ^ 2 * g.ωc ^ 2, g.D ^ 2 * g.M + g.D * g.M ^ 2 * g.ωc + g.M ^ 3 * g.ωc ^ 2,
        g.D * g.M - g.M ^ 2 * g.ωc;
      -(g.D * g.M * g.ωc), g.D * g.M - g.M ^ 2 * g.ωc, 2 * g.M] with hQ
  set ℓ : Fin 3 → ℝ := ![-(g.D * g.ωc), g.D, 1] with hℓ
  have hS : -((g.jacobian δ)ᵀ * Q + Q * g.jacobian δ) =
      (2 * (g.D + g.M * g.ωc)) • vecMulVec ℓ ℓ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hQ, hℓ, jacobian, Matrix.mul_apply, Fin.sum_univ_three, hk, vecMulVec] <;>
      field_simp <;> ring
  refine ⟨Q, Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ]
  · simp only [star_trivial]
    set a := -(g.M * g.ωc) * x 1 + x 2
    set b := (g.D + g.M * g.ωc) * x 0 + g.M * x 1
    set c := -(g.D * g.ωc) * x 0 + g.D * x 1 + x 2
    have e : x ⬝ᵥ (Q *ᵥ x) = g.M * a ^ 2 + g.D * g.ωc * b ^ 2 + g.M * c ^ 2 := by
      simp [hQ, dotProduct, mulVec, Fin.sum_univ_three, a, b, c]; ring
    rw [e]
    by_contra hle
    have h1 : 0 ≤ g.M * a ^ 2 := by positivity
    have h2 : 0 ≤ g.D * g.ωc * b ^ 2 := by positivity
    have h3 : 0 ≤ g.M * c ^ 2 := by positivity
    have sq0 : ∀ {k t : ℝ}, 0 < k → k * t ^ 2 = 0 → t = 0 := fun hk ht =>
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp ht).resolve_left hk.ne')
    have ha : a = 0 := sq0 hM (by linarith)
    have hb : b = 0 := sq0 (k := g.D * g.ωc) (by positivity) (by linarith)
    have hc : c = 0 := sq0 hM (by linarith)
    have hx0' : x 0 * ((g.D + g.M * g.ωc) ^ 2 + g.D * g.M * g.ωc) = 0 := by
      linear_combination (g.D + g.M * g.ωc) * hb - g.M * hc + g.M * ha
    have hpos : 0 < (g.D + g.M * g.ωc) ^ 2 + g.D * g.M * g.ωc := by positivity
    have hx0 : x 0 = 0 := (mul_eq_zero.mp hx0').resolve_right hpos.ne'
    have hx1 : x 1 = 0 := by
      have : g.M * x 1 = 0 := by rw [← hb]; simp [b, hx0]
      exact (mul_eq_zero.mp this).resolve_left hM'
    have hx2 : x 2 = 0 := by rw [← ha]; simp [a, hx1]
    exact hx (funext fun i => by fin_cases i <;> simp [hx0, hx1, hx2])
  · rw [hS]
    have hv : (vecMulVec ℓ ℓ).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star ℓ
    exact hv.smul (by positivity)

/-- **Linear pH form with `R ⪰ 0` iff the closed Routh region.** For positive `M, D, ω_c`, the
Jacobian at angle `δ` is `(J − R) Q` with `J` skew, `R ⪰ 0`, `Q ≻ 0` iff
`0 ≤ K₀ cos δ ≤ D ω_c + D²/M`. Both boundary values are included: inside, the form with
`R ≻ 0` (`exists_linearPH_jacobian_iff`); on the boundary, explicit Lyapunov matrices through
`PH.exists_linearPH_posSemidef_iff`; outside, `linearPH_jacobian_bounds`. -/
@[tmio M, powerlib_domain] theorem exists_linearPH_posSemidef_jacobian_iff (hM : 0 < g.M)
    (hD : 0 < g.D) (hωc : 0 < g.ωc) (δ : ℝ) :
    (∃ J R Q : Matrix (Fin 3) (Fin 3) ℝ, Jᵀ = -J ∧ R.PosSemidef ∧ Q.PosDef ∧
      PH.linearStateMatrix J R Q = g.jacobian δ) ↔
      0 ≤ g.K0 * Real.cos δ ∧ g.K0 * Real.cos δ ≤ g.D * g.ωc + g.D ^ 2 / g.M := by
  refine ⟨g.linearPH_jacobian_bounds hM hωc, fun ⟨h0, h1⟩ => ?_⟩
  rcases h0.eq_or_lt with h0 | h0
  · exact (PH.exists_linearPH_posSemidef_iff _).mpr
      (g.lyapunov_jacobian_of_eq_zero hM hD hωc h0.symm)
  rcases h1.eq_or_lt with h1 | h1
  · exact (PH.exists_linearPH_posSemidef_iff _).mpr
      (g.lyapunov_jacobian_of_eq_routh hM hD hωc h1)
  obtain ⟨J, R, Q, hJ, hR, hQ, hA⟩ := (g.exists_linearPH_jacobian_iff hM hD hωc δ).mpr ⟨h0, h1⟩
  exact ⟨J, R, Q, hJ, hR.posSemidef, hQ, hA⟩

end VSMLPF

end powerlib.GFM
