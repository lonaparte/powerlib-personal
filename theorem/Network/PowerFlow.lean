import theorem.Attributes
import dependencies.Mathlib
import theorem.Network.WeightedLaplacian

/-! # Power flow: the lossless injection map, two-bus line powers, the decoupling rotation

Static foundation: the lossless active-power injection map of a network, and identities and
derivatives of the complex power `S̄ = V̄ Ī*` carried by one line between two voltage phasors.
No model family is defined and no behavioural sentence is stated.

Model boundary.
* Network: lossless lines, constant voltage magnitudes absorbed into `bᵢⱼ = VᵢVⱼ/Xᵢⱼ`, active
  power only.
* One line: source `E ∠ δ` through `Z = R + jX` into `V ∠ 0`; the converter-side and grid-side
  identities use a purely reactive line `X` from `V e^{jθ}` to `V_g` (export current
  `Ī = (V e^{jθ} − V_g)/(jX)`).
* Phasor (steady-state) level: no line or machine dynamics.

Source: work-sync `theory/T-droop-control.md` §1.2, §1.5;
`theory/T-power-synchronization-control.md` §1.1; the injection map as in
`theory/T-synchronization-manifold.md` §1.7 and `theory/T-local-frequency.md` §1.2–§1.5.

Results.
* `powerInjection`: the lossless injections `Pᵢ(θ) = ∑ⱼ bᵢⱼ sin(θᵢ − θⱼ)`; its Jacobian is the
  weighted Laplacian (`theorem/Network/WeightedLaplacian.lean`) of the linearization weights
  `flowWeights b θ = bᵢⱼ cos(θᵢ − θⱼ)` (`hasFDerivAt_powerInjection`). Used by the networked
  swing equations (`theorem/Network/Swing/`) and the frequency divider
  (`theorem/Network/FrequencyDivider.lean`).
* `linePower`: the power exported from the source `E ∠ δ` through `Z = R + jX` into `V ∠ 0`;
  its active and reactive parts `lineP`, `lineQ` and their partial derivatives at `δ = 0`,
  `E = V` (`lineP_deriv_delta`, `lineP_deriv_E`, `lineQ_deriv_delta`, `lineQ_deriv_E`).
* `rotation_diagonalizes`: the rotation `R(β)`, `β = π/2 − θ_l` (`cos θ_l = R/|Z|`,
  `sin θ_l = X/|Z|`), diagonalizes that Jacobian; inductive line (`θ_l = π/2`): `R(β) = I`
  (`rotation_inductive`, classical P–f / Q–V droop); resistive line (`θ_l = 0`):
  `(P̂, Q̂) = (−Q, P)` (`rotation_resistive`, inverse droop).
* Purely reactive line: the converter-side power `S̄ = V̄_conv Ī*`, `P = V V_g sin θ / X`,
  `Q_conv = (V² − V V_g cos θ)/X` (`converterSide_power`), and the power received at the grid
  bus `S̄_g = V̄_g Ī*`, `Q_g = (V V_g cos θ − V_g²)/X` (`gridSide_power`).
* The rotated droop of `theorem/GFM/DroopAlgebra.lean` and the reactive-power correction of
  `theorem/GFM/PSC.lean` refer to these identities.
-/

noncomputable section
namespace powerlib.Network

/-! ## Linearized power flow -/

section Injection

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lossless active-power injections `Pᵢ(θ) = ∑ⱼ bᵢⱼ sin(θᵢ - θⱼ)` (voltage magnitudes,
held constant, are absorbed into `bᵢⱼ = VᵢVⱼ/Xᵢⱼ`). -/
def powerInjection (b : Matrix ι ι ℝ) (θ : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, b i j * Real.sin (θ i - θ j)

/-- Linearization weights `bᵢⱼ cos(θᵢ⁰ - θⱼ⁰)`. -/
def flowWeights (b : Matrix ι ι ℝ) (θ : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => b i j * Real.cos (θ i - θ j)

/-- The Jacobian of the lossless power-flow map is the weighted Laplacian of
`bᵢⱼ cos(θᵢ - θⱼ)`. -/
@[powerlib_foundation] theorem hasFDerivAt_powerInjection (b : Matrix ι ι ℝ) (θ : ι → ℝ) :
    HasFDerivAt (powerInjection b)
      (Matrix.toLin' (laplacian (flowWeights b θ))).toContinuousLinearMap θ := by
  rw [hasFDerivAt_pi']
  intro i
  have hterm : ∀ j ∈ (Finset.univ : Finset ι), HasFDerivAt
      (fun φ : ι → ℝ => b i j * Real.sin (φ i - φ j))
      ((b i j * Real.cos (θ i - θ j)) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)) θ := by
    intro j _
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) i θ).sub
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) j θ)).sin.const_mul (b i j)
    convert hd using 1
    ext v
    simp [smul_eq_mul]
    ring
  convert HasFDerivAt.fun_sum hterm using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, laplacian_mulVec_apply,
      flowWeights, of_apply, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sub, Pi.sub_apply,
      smul_eq_mul]

end Injection

/-! ## Two-bus line power and the decoupling rotation -/

section LinePower

open Complex

/-- Export power from `E ∠ δ` through `Z = R + jX` into `V ∠ 0`, from `S̄ = Ē Ī*`. -/
@[powerlib_foundation] theorem linePower (E V δ R X : ℝ) (hZ : R ^ 2 + X ^ 2 ≠ 0) :
    (E : ℂ) * exp (δ * I) *
        (starRingEnd ℂ) (((E : ℂ) * exp (δ * I) - (V : ℂ)) / ((R : ℂ) + (X : ℂ) * I)) =
      (((R * (E ^ 2 - E * V * Real.cos δ) + X * E * V * Real.sin δ) / (R ^ 2 + X ^ 2) : ℝ) : ℂ) +
        (((X * (E ^ 2 - E * V * Real.cos δ) - R * E * V * Real.sin δ) / (R ^ 2 + X ^ 2) : ℝ) : ℂ) *
          I := by
  have hZ' : R * R + X * X ≠ 0 := by simpa [sq] using hZ
  have hsc := Real.sin_sq_add_cos_sq δ
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, mul_zero, zero_mul,
      sub_zero, add_zero, zero_add, mul_one] <;>
    field_simp
  · linear_combination (E ^ 2 * R) * hsc
  · linear_combination (E ^ 2 * X) * hsc

/-- Active line power `P(δ, E)`. -/
def lineP (V R X : ℝ) (δ E : ℝ) : ℝ :=
  (R * (E ^ 2 - E * V * Real.cos δ) + X * E * V * Real.sin δ) / (R ^ 2 + X ^ 2)

/-- Reactive line power `Q(δ, E)`. -/
def lineQ (V R X : ℝ) (δ E : ℝ) : ℝ :=
  (X * (E ^ 2 - E * V * Real.cos δ) - R * E * V * Real.sin δ) / (R ^ 2 + X ^ 2)

@[powerlib_foundation] theorem lineP_deriv_delta (V R X : ℝ) :
    HasDerivAt (fun δ => lineP V R X δ V) (X * V ^ 2 / (R ^ 2 + X ^ 2)) 0 := by
  have h := ((((Real.hasDerivAt_cos 0).const_mul (V * V)).const_sub (V ^ 2)).const_mul R).add
    ((Real.hasDerivAt_sin 0).const_mul (X * V * V)) |>.div_const (R ^ 2 + X ^ 2)
  convert h using 1
  · funext δ; simp only [lineP, Pi.add_apply]
  · simp; ring

@[powerlib_foundation] theorem lineP_deriv_E (V R X : ℝ) :
    HasDerivAt (fun E => lineP V R X 0 E) (R * V / (R ^ 2 + X ^ 2)) V := by
  have h := ((((hasDerivAt_id V).pow 2).sub ((hasDerivAt_id V).mul_const V)).const_mul R)
    |>.div_const (R ^ 2 + X ^ 2)
  convert h using 1
  · funext E; simp [lineP]
  · simp; ring

@[powerlib_foundation] theorem lineQ_deriv_delta (V R X : ℝ) :
    HasDerivAt (fun δ => lineQ V R X δ V) (-(R * V ^ 2) / (R ^ 2 + X ^ 2)) 0 := by
  have h := ((((Real.hasDerivAt_cos 0).const_mul (V * V)).const_sub (V ^ 2)).const_mul X).sub
    ((Real.hasDerivAt_sin 0).const_mul (R * V * V)) |>.div_const (R ^ 2 + X ^ 2)
  convert h using 1
  · funext δ; simp only [lineQ, Pi.sub_apply]
  · simp; ring

@[powerlib_foundation] theorem lineQ_deriv_E (V R X : ℝ) :
    HasDerivAt (fun E => lineQ V R X 0 E) (X * V / (R ^ 2 + X ^ 2)) V := by
  have h := ((((hasDerivAt_id V).pow 2).sub ((hasDerivAt_id V).mul_const V)).const_mul X)
    |>.div_const (R ^ 2 + X ^ 2)
  convert h using 1
  · funext E; simp [lineQ]
  · simp; ring

/-- The rotation `R(β)`, `β = π/2 − θ_l` with `cos θ_l = R/|Z|`, `sin θ_l = X/|Z|`,
diagonalizes the line Jacobian `[[X V², R V], [−R V², X V]] / |Z|²`:
`R(β) J = (V/|Z|) diag(V, 1)`. -/
@[powerlib_foundation] theorem rotation_diagonalizes {V R X z θl : ℝ} (hz : 0 < z)
    (hz2 : z ^ 2 = R ^ 2 + X ^ 2) (hc : Real.cos θl = R / z) (hs : Real.sin θl = X / z) :
    !![Real.cos (Real.pi / 2 - θl), -Real.sin (Real.pi / 2 - θl);
        Real.sin (Real.pi / 2 - θl), Real.cos (Real.pi / 2 - θl)] *
      !![X * V ^ 2 / (R ^ 2 + X ^ 2), R * V / (R ^ 2 + X ^ 2);
        -(R * V ^ 2) / (R ^ 2 + X ^ 2), X * V / (R ^ 2 + X ^ 2)] =
      !![V / z * V, 0; 0, V / z] := by
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hc, hs, ← hz2]
  have hz' := hz.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  · linear_combination (-V ^ 2) * hz2
  · ring
  · ring
  · linear_combination (-V) * hz2

/-- Inductive line (`θ_l = π/2`): the rotation is the identity (classical P–f / Q–V droop). -/
@[powerlib_foundation] theorem rotation_inductive :
    !![Real.cos (Real.pi / 2 - Real.pi / 2), -Real.sin (Real.pi / 2 - Real.pi / 2);
        Real.sin (Real.pi / 2 - Real.pi / 2), Real.cos (Real.pi / 2 - Real.pi / 2)] =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Resistive line (`θ_l = 0`): `(P̂, Q̂) = R(π/2)(P, Q) = (−Q, P)` (inverse droop). -/
@[powerlib_foundation] theorem rotation_resistive (P Q : ℝ) :
    Matrix.mulVec !![Real.cos (Real.pi / 2 - 0), -Real.sin (Real.pi / 2 - 0);
        Real.sin (Real.pi / 2 - 0), Real.cos (Real.pi / 2 - 0)] ![P, Q] = ![-Q, P] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end LinePower

/-! ## Converter-side and grid-side power over a reactance -/

/-- Converter-side complex power `S̄ = V̄_conv Ī*`, `Ī = (V e^{jθ} − V_g)/(jX)` (export current):
`P = V V_g sin θ / X`, `Q_conv = (V² − V V_g cos θ)/X`. -/
@[powerlib_foundation] theorem converterSide_power (V Vg θ X : ℝ) (hX : X ≠ 0) :
    (V : ℂ) * Complex.exp (θ * Complex.I) *
        (starRingEnd ℂ) (((V : ℂ) * Complex.exp (θ * Complex.I) - (Vg : ℂ)) /
          ((X : ℂ) * Complex.I)) =
      ((V * Vg * Real.sin θ / X : ℝ) : ℂ) +
        ((V ^ 2 - V * Vg * Real.cos θ) / X : ℝ) * Complex.I := by
  rw [show V ^ 2 - V * Vg * Real.cos θ =
      V ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) - V * Vg * Real.cos θ by
    rw [Real.sin_sq_add_cos_sq]; ring]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;>
    field_simp <;> ring

/-- Grid-side received complex power `S̄_g = V̄_g Ī*`: `P = V V_g sin θ / X`,
`Q_g = (V V_g cos θ − V_g²)/X` (the note's `Q₀`). -/
@[powerlib_foundation] theorem gridSide_power (V Vg θ X : ℝ) (hX : X ≠ 0) :
    (Vg : ℂ) * (starRingEnd ℂ) (((V : ℂ) * Complex.exp (θ * Complex.I) - (Vg : ℂ)) /
          ((X : ℂ) * Complex.I)) =
      ((V * Vg * Real.sin θ / X : ℝ) : ℂ) +
        ((V * Vg * Real.cos θ - Vg ^ 2) / X : ℝ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;>
    field_simp <;> ring

end powerlib.Network
