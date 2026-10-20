import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.RealDeriv

/-! # Frequency-domain line: propagation, ABCD chain matrix, port impedances

The phasor line equations at one complex frequency: exact propagation solution, the ABCD chain
matrix and its cascade law, port impedances, the exact Π equivalent, and the multi-conductor
second-order equations.

Model boundary.
* Uniform single-conductor line at one fixed complex frequency `s`; per-unit-length
  series impedance `Z = R' + sL'` and shunt admittance `Y = G' + sC'` are constants in `ℂ`.
* The phasor line equations are the constant-coefficient ODE in `x ∈ ℝ`,
  `V' = -Z I`, `I' = -Y V` (no Laplace transform or PDE is invoked: the ODE in `x` is the
  model). `I(x)` is the current along `+x`; at end 2 the current `I₂ = I(ℓ)` flows out
  (through convention, so that chain matrices multiply in cascade).
* Propagation constant and characteristic impedance are any pair `(γ, Z_c)` with
  `Z_c ≠ 0`, `γ = Z_c Y`, `Z = Z_c γ` (so `γ² = ZY`, `Z_c² Y = Z`). For `Z, Y ≠ 0` such a pair
  exists (`exists_params`) with the principal square root `Z_c = (Z/Y)^{1/2}`; the sign of
  the square root is immaterial for every identity below.

Source: work-sync `theory/T-telegrapher-bergeron.md` §1.2, §1.3, §1.3.1, §1.3.2, §1.7.2, §1.8;
`theory/T-pde-systems.md` §1.4.5.

Results.
* Exact solution of the line ODE (`propagation_solves`) and its uniqueness (`eq_propagation`).
* The ABCD relation `[V₁; I₁] = T [V₂; I₂]` (`chain_relation`), `det T = 1` (`det_chain`),
  `A = D` (`chain_A_eq_D`), `BC = sinh²` (`chain_B_mul_C`), cascade `T(ℓ₁)T(ℓ₂) = T(ℓ₁+ℓ₂)`
  (`chain_mul`, `cascade_relation`).
* Short/open-circuit impedances and parameter inversion (`shortCircuit`, `openCircuit`,
  `Zsc_mul_Zoc`, `Zsc_div_Zoc`, `exp_two_mul_gammaL`, `two_mul_gammaL_eq_log_add`).
* Exact Π equivalent and its short-line limit (`piChain_exact`, `piSeries_shortLine`,
  `piShunt_shortLine`); input impedance with a load (`input_relation`,
  `inputImpedance_tanh`, `matched_inputImpedance`, `lossless_quarterWave`).
* Multi-conductor second-order equations (`multiconductor_second_order`).

Corrections.
* Parameter inversion (§1.3.1): `γℓ = ½ ln((1+ρ)/(1-ρ))` holds only modulo `iπℤ`
  (`exp (2γℓ) = (1+ρ)/(1-ρ)`, `two_mul_gammaL_eq_log_add`), and `ρ` must be `Z_sc/Z_c`
  (`= tanh γℓ`); `ρ = √(Z_sc/Z_oc)` determines it only up to sign.
* §1.8 "`tanh` 是整函数": wrong, `tanh` is meromorphic; it is not even continuous at
  `iπ/2` (`tanh_not_continuousAt`).
* §1.8 "`Z_in` 极点在四分之一波长": the denominator of `Z_in` is `Z_c cosh γℓ + Z_L sinh γℓ`; it
  vanishes on the quarter-wave set `cosh γℓ = 0` only for `Z_L = 0`
  (`shorted_denominator_zero_iff`). A matched load `Z_L = Z_c` gives no pole at all and
  `Z_in = Z_c` (`matched_inputImpedance`).
* §1.7.2 matrix ABCD: with matrix-valued `Z, Y` the voltage satisfies `V'' = ZY V` while the
  current satisfies `I'' = YZ I` (`multiconductor_second_order`), so the (2,2) block of the
  chain matrix is `cosh(Γ'ℓ)` with `Γ'² = YZ`, not `cosh(Γℓ)` with `Γ² = ZY`, unless
  `ZY = YZ`, which fails in general (`matrix_mul_not_comm_example`).
-/

noncomputable section
namespace powerlib.Line.Phasor
open Complex Matrix

/-- Line parameters at one frequency. -/
structure Params where
  Z : ℂ
  Y : ℂ
  γ : ℂ
  Zc : ℂ
  Zc_ne : Zc ≠ 0
  hγ : γ = Zc * Y
  hZ : Z = Zc * γ

variable (p : Params)

@[powerlib_foundation] theorem gamma_sq : p.γ ^ 2 = p.Z * p.Y := by
  rw [p.hZ, p.hγ]; ring

@[powerlib_foundation] theorem Zc_sq_mul_Y : p.Zc ^ 2 * p.Y = p.Z := by
  rw [p.hZ, p.hγ]; ring

/-- Parameters exist for every line with `Z ≠ 0`, `Y ≠ 0` (principal square root). -/
@[powerlib_foundation] theorem exists_params {Z Y : ℂ} (hZ : Z ≠ 0) (hY : Y ≠ 0) :
    ∃ q : Params, q.Z = Z ∧ q.Y = Y ∧ q.Zc = (Z / Y) ^ ((2 : ℂ)⁻¹) := by
  have hsq : ((Z / Y) ^ ((2 : ℂ)⁻¹)) ^ 2 = Z / Y := cpow_ofNat_inv_pow (Z / Y) 2
  have hne : (Z / Y) ^ ((2 : ℂ)⁻¹) ≠ 0 := by
    intro h; rw [h] at hsq; simp at hsq; exact div_ne_zero hZ hY hsq.symm
  refine ⟨⟨Z, Y, (Z / Y) ^ ((2 : ℂ)⁻¹) * Y, (Z / Y) ^ ((2 : ℂ)⁻¹), hne, rfl, ?_⟩, rfl, rfl, rfl⟩
  calc Z = (Z / Y) * Y := (div_mul_cancel₀ Z hY).symm
    _ = ((Z / Y) ^ ((2 : ℂ)⁻¹)) ^ 2 * Y := by rw [hsq]
    _ = _ := by ring

/-! ## Solution of the line ODE -/

/-- Voltage profile with sending-end data `(V₀, I₀)`. -/
def voltage (V₀ I₀ : ℂ) (x : ℝ) : ℂ := V₀ * cosh (p.γ * x) - p.Zc * I₀ * sinh (p.γ * x)

/-- Current profile with sending-end data `(V₀, I₀)`. -/
def current (V₀ I₀ : ℂ) (x : ℝ) : ℂ := I₀ * cosh (p.γ * x) - V₀ / p.Zc * sinh (p.γ * x)

@[powerlib_foundation] theorem hasDerivAt_cosh_mul (γ : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosh (γ * y)) (γ * sinh (γ * x)) x := by
  have hl : HasDerivAt (fun y : ℝ => γ * (y : ℂ)) γ x := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul γ).comp_ofReal
  have := HasDerivAt.comp x (Complex.hasDerivAt_cosh (γ * x)) hl
  simpa [Function.comp_def, mul_comm] using this

@[powerlib_foundation] theorem hasDerivAt_sinh_mul (γ : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => sinh (γ * y)) (γ * cosh (γ * x)) x := by
  have hl : HasDerivAt (fun y : ℝ => γ * (y : ℂ)) γ x := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul γ).comp_ofReal
  have := HasDerivAt.comp x (Complex.hasDerivAt_sinh (γ * x)) hl
  simpa [Function.comp_def, mul_comm] using this

/-- The propagation profiles solve `V' = -Z I`, `I' = -Y V`. -/
@[powerlib_foundation] theorem propagation_solves (V₀ I₀ : ℂ) (x : ℝ) :
    HasDerivAt (voltage p V₀ I₀) (-p.Z * current p V₀ I₀ x) x ∧
      HasDerivAt (current p V₀ I₀) (-p.Y * voltage p V₀ I₀ x) x := by
  have hc := hasDerivAt_cosh_mul p.γ x
  have hs := hasDerivAt_sinh_mul p.γ x
  have hZc := p.Zc_ne
  have hY : p.Y = p.γ / p.Zc := by rw [p.hγ]; field_simp
  constructor
  · refine ((hc.const_mul V₀).sub (hs.const_mul (p.Zc * I₀))).congr_deriv ?_
    rw [p.hZ]; simp only [current]; field_simp; ring
  · refine ((hc.const_mul I₀).sub (hs.const_mul (V₀ / p.Zc))).congr_deriv ?_
    rw [hY]; simp only [voltage]; field_simp; ring

@[powerlib_foundation] theorem propagation_zero (V₀ I₀ : ℂ) :
    voltage p V₀ I₀ 0 = V₀ ∧ current p V₀ I₀ 0 = I₀ := by
  simp [voltage, current]

/-- Uniqueness: every solution of the line ODE is the propagation of its sending-end data. -/
@[powerlib_foundation] theorem eq_propagation {V I : ℝ → ℂ}
    (hV : ∀ x, HasDerivAt V (-p.Z * I x) x) (hI : ∀ x, HasDerivAt I (-p.Y * V x) x) (x : ℝ) :
    V x = voltage p (V 0) (I 0) x ∧ I x = current p (V 0) (I 0) x := by
  let F : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
    ((-p.Z) • (ContinuousLinearMap.snd ℝ ℂ ℂ).restrictScalars ℝ |>.prod
      ((-p.Y) • (ContinuousLinearMap.fst ℝ ℂ ℂ)))
  have hF : ∀ w : ℂ × ℂ, F w = (-p.Z * w.2, -p.Y * w.1) := fun w => by
    simp [F]
  have hsol : ∀ (W : ℝ → ℂ × ℂ), (∀ x, HasDerivAt (fun y => (W y).1) (-p.Z * (W x).2) x) →
      (∀ x, HasDerivAt (fun y => (W y).2) (-p.Y * (W x).1) x) →
      ∀ x, HasDerivAt W (F (W x)) x ∧ W x ∈ (Set.univ : Set (ℂ × ℂ)) := by
    intro W h1 h2 x
    refine ⟨?_, trivial⟩
    rw [hF]
    exact (h1 x).prodMk (h2 x)
  have huniq := ODE_solution_unique_univ (v := fun _ => F) (s := fun _ => Set.univ)
    (K := ‖F‖₊) (f := fun y => (V y, I y))
    (g := fun y => (voltage p (V 0) (I 0) y, current p (V 0) (I 0) y)) (t₀ := 0)
    (fun _ => F.lipschitzWith.lipschitzOnWith)
    (hsol _ (fun y => hV y) (fun y => hI y))
    (hsol _ (fun y => (propagation_solves p (V 0) (I 0) y).1)
      (fun y => (propagation_solves p (V 0) (I 0) y).2))
    (by simp [propagation_zero])
  have := congrFun huniq x
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-! ## ABCD chain matrix -/

/-- Chain (ABCD) matrix of a line section of length `ℓ`. -/
def chain (ℓ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![cosh (p.γ * ℓ), p.Zc * sinh (p.γ * ℓ); sinh (p.γ * ℓ) / p.Zc, cosh (p.γ * ℓ)]

/-- **ABCD relation**: the sending-end quantities are the chain matrix applied to the
receiving-end quantities (`I₂` leaving end 2). -/
@[powerlib_foundation] theorem chain_relation (V₀ I₀ : ℂ) (ℓ : ℝ) :
    ![V₀, I₀] = chain p ℓ *ᵥ ![voltage p V₀ I₀ ℓ, current p V₀ I₀ ℓ] := by
  have hinv : p.Zc * p.Zc⁻¹ = 1 := mul_inv_cancel₀ p.Zc_ne
  have h := Complex.cosh_sq_sub_sinh_sq (p.γ * ℓ)
  ext i
  fin_cases i
  · simp only [chain, voltage, current, mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta,
      Fin.isValue, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, div_eq_mul_inv]
    linear_combination -V₀ * h + V₀ * sinh (p.γ * ℓ) ^ 2 * hinv
  · simp only [chain, voltage, current, mulVec, dotProduct, Fin.sum_univ_two, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, div_eq_mul_inv]
    linear_combination -I₀ * h + I₀ * sinh (p.γ * ℓ) ^ 2 * hinv

/-- `det T = 1` (reciprocity). -/
@[powerlib_foundation] theorem det_chain (ℓ : ℂ) : (chain p ℓ).det = 1 := by
  have hinv : p.Zc * p.Zc⁻¹ = 1 := mul_inv_cancel₀ p.Zc_ne
  rw [chain, det_fin_two_of, div_eq_mul_inv]
  linear_combination Complex.cosh_sq_sub_sinh_sq (p.γ * ℓ) - sinh (p.γ * ℓ) ^ 2 * hinv

/-- `A = D` (symmetric two-port). -/
@[powerlib_foundation] theorem chain_A_eq_D (ℓ : ℂ) : chain p ℓ 0 0 = chain p ℓ 1 1 := by
  simp [chain]

/-- `B · C = sinh²(γℓ)`. -/
@[powerlib_foundation] theorem chain_B_mul_C (ℓ : ℂ) :
    chain p ℓ 0 1 * chain p ℓ 1 0 = sinh (p.γ * ℓ) ^ 2 := by
  have hZc := p.Zc_ne
  simp [chain]
  field_simp

/-- Cascade of two sections of the same line: `T(ℓ₁) T(ℓ₂) = T(ℓ₁ + ℓ₂)`. -/
@[powerlib_foundation] theorem chain_mul (ℓ₁ ℓ₂ : ℂ) :
    chain p ℓ₁ * chain p ℓ₂ = chain p (ℓ₁ + ℓ₂) := by
  have hZc := p.Zc_ne
  rw [chain, chain, chain, mul_add, Complex.cosh_add, Complex.sinh_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Chain matrices of cascaded two-ports multiply. -/
@[powerlib_foundation] theorem cascade_relation {T₁ T₂ : Matrix (Fin 2) (Fin 2) ℂ}
    {X₀ X₁ X₂ : Fin 2 → ℂ} (h₁ : X₀ = T₁ *ᵥ X₁) (h₂ : X₁ = T₂ *ᵥ X₂) :
    X₀ = (T₁ * T₂) *ᵥ X₂ := by
  rw [h₁, h₂, mulVec_mulVec]

/-! ## Short- and open-circuit impedances -/

/-- Short-circuit input impedance: with `V₂ = 0`, `V₁ = Z_c tanh(γℓ) I₁`. -/
@[powerlib_foundation] theorem shortCircuit (ℓ : ℂ) (I₂ : ℂ) (hc : cosh (p.γ * ℓ) ≠ 0) :
    (chain p ℓ *ᵥ ![0, I₂]) 0 = p.Zc * tanh (p.γ * ℓ) * (chain p ℓ *ᵥ ![0, I₂]) 1 := by
  simp [chain, mulVec, dotProduct, Fin.sum_univ_two, Complex.tanh_eq_sinh_div_cosh]
  field_simp

/-- Open-circuit input impedance: with `I₂ = 0`, `sinh(γℓ) V₁ = Z_c cosh(γℓ) I₁`
(`Z_oc = Z_c coth γℓ` when `sinh γℓ ≠ 0`). -/
@[powerlib_foundation] theorem openCircuit (ℓ : ℂ) (V₂ : ℂ) :
    sinh (p.γ * ℓ) * (chain p ℓ *ᵥ ![V₂, 0]) 0 =
      p.Zc * cosh (p.γ * ℓ) * (chain p ℓ *ᵥ ![V₂, 0]) 1 := by
  have hZc := p.Zc_ne
  simp [chain, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp

/-- `Z_sc = Z_c tanh γℓ`. -/
def Zsc (ℓ : ℂ) : ℂ := p.Zc * tanh (p.γ * ℓ)
/-- `Z_oc = Z_c cosh γℓ / sinh γℓ`. -/
def Zoc (ℓ : ℂ) : ℂ := p.Zc * cosh (p.γ * ℓ) / sinh (p.γ * ℓ)

/-- Parameter identification: `Z_sc Z_oc = Z_c²`. -/
@[powerlib_foundation] theorem Zsc_mul_Zoc (ℓ : ℂ) (hc : cosh (p.γ * ℓ) ≠ 0)
    (hs : sinh (p.γ * ℓ) ≠ 0) : Zsc p ℓ * Zoc p ℓ = p.Zc ^ 2 := by
  simp only [Zsc, Zoc, Complex.tanh_eq_sinh_div_cosh]
  field_simp

/-- `Z_sc / Z_oc = tanh²(γℓ)`. -/
@[powerlib_foundation] theorem Zsc_div_Zoc (ℓ : ℂ) (hc : cosh (p.γ * ℓ) ≠ 0)
    (hs : sinh (p.γ * ℓ) ≠ 0) : Zsc p ℓ / Zoc p ℓ = tanh (p.γ * ℓ) ^ 2 := by
  have hZc := p.Zc_ne
  simp only [Zsc, Zoc, Complex.tanh_eq_sinh_div_cosh]
  field_simp

/-- With `ρ = Z_sc/Z_c = tanh γℓ`: `exp(2γℓ) = (1+ρ)/(1-ρ)`. -/
@[powerlib_foundation] theorem exp_two_mul_gammaL (ℓ : ℂ) (hc : cosh (p.γ * ℓ) ≠ 0) :
    1 - Zsc p ℓ / p.Zc ≠ 0 ∧
      exp (2 * (p.γ * ℓ)) = (1 + Zsc p ℓ / p.Zc) / (1 - Zsc p ℓ / p.Zc) := by
  have hZc := p.Zc_ne
  have hρ : Zsc p ℓ / p.Zc = sinh (p.γ * ℓ) / cosh (p.γ * ℓ) := by
    simp only [Zsc, Complex.tanh_eq_sinh_div_cosh]; field_simp
  have hcm : cosh (p.γ * ℓ) - sinh (p.γ * ℓ) = exp (-(p.γ * ℓ)) := by
    rw [← Complex.cosh_neg, ← Complex.cosh_add_sinh, Complex.cosh_neg, Complex.sinh_neg]; ring
  have hcp : cosh (p.γ * ℓ) + sinh (p.γ * ℓ) = exp (p.γ * ℓ) := Complex.cosh_add_sinh _
  have hden : 1 - Zsc p ℓ / p.Zc = exp (-(p.γ * ℓ)) / cosh (p.γ * ℓ) := by
    rw [hρ, ← hcm]; field_simp
  have hnum : 1 + Zsc p ℓ / p.Zc = exp (p.γ * ℓ) / cosh (p.γ * ℓ) := by
    rw [hρ, ← hcp]; field_simp
  refine ⟨by rw [hden]; exact div_ne_zero (Complex.exp_ne_zero _) hc, ?_⟩
  rw [hnum, hden, div_div_div_cancel_right₀ hc, ← Complex.exp_sub]
  ring_nf

/-- Correction to `γℓ = ½ ln((1+ρ)/(1-ρ))`: the identity holds modulo `iπℤ`. -/
@[powerlib_foundation] theorem two_mul_gammaL_eq_log_add (ℓ : ℂ) (hc : cosh (p.γ * ℓ) ≠ 0) :
    ∃ k : ℤ, 2 * (p.γ * ℓ) =
      log ((1 + Zsc p ℓ / p.Zc) / (1 - Zsc p ℓ / p.Zc)) + k * (2 * Real.pi * I) := by
  obtain ⟨-, h⟩ := exp_two_mul_gammaL p ℓ hc
  have hq : (1 + Zsc p ℓ / p.Zc) / (1 - Zsc p ℓ / p.Zc) ≠ 0 := by
    rw [← h]; exact Complex.exp_ne_zero _
  have := Complex.exp_eq_exp_iff_exists_int.mp (h.trans (Complex.exp_log hq).symm)
  exact this

/-! ## Exact Π equivalent -/

/-- Chain matrix of a Π network: shunt `Y_sh`, series `Z_s`, shunt `Y_sh`. -/
def piChain (Zs Ysh : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; Ysh, 1] * !![1, Zs; 0, 1] * !![1, 0; Ysh, 1]

@[powerlib_foundation] theorem piChain_eq (Zs Ysh : ℂ) :
    piChain Zs Ysh = !![1 + Zs * Ysh, Zs; Ysh * (2 + Zs * Ysh), 1 + Zs * Ysh] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [piChain, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Exact Π equivalent** (one frequency): `Z_s = Z_c sinh γℓ`, `Y_sh = tanh(γℓ/2)/Z_c`. -/
@[powerlib_foundation] theorem piChain_exact (ℓ : ℂ) (hc : cosh (p.γ * ℓ / 2) ≠ 0) :
    piChain (p.Zc * sinh (p.γ * ℓ)) (tanh (p.γ * ℓ / 2) / p.Zc) = chain p ℓ := by
  have hZc := p.Zc_ne
  have hs : sinh (p.γ * ℓ) = 2 * sinh (p.γ * ℓ / 2) * cosh (p.γ * ℓ / 2) := by
    rw [← Complex.sinh_two_mul]; ring_nf
  have hcosh : cosh (p.γ * ℓ) = cosh (p.γ * ℓ / 2) ^ 2 + sinh (p.γ * ℓ / 2) ^ 2 := by
    rw [← Complex.cosh_two_mul]; ring_nf
  have hsq := Complex.cosh_sq_sub_sinh_sq (p.γ * ℓ / 2)
  rw [piChain_eq, chain, hs, hcosh, Complex.tanh_eq_sinh_div_cosh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · linear_combination -hsq
  · linear_combination -sinh (p.γ * ℓ / 2) * hsq
  · linear_combination -hsq

/-- Short-line limit of the exact series branch: `Z_s(ℓ) = Z_c sinh γℓ = Zℓ + o(ℓ)`. -/
@[powerlib_foundation] theorem piSeries_shortLine :
    HasDerivAt (fun ℓ : ℂ => p.Zc * sinh (p.γ * ℓ)) p.Z 0 := by
  have h := ((Complex.hasDerivAt_sinh (p.γ * 0)).comp (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).const_mul p.γ)).const_mul p.Zc
  simp only [mul_zero, Complex.cosh_zero, one_mul, mul_one] at h
  rw [p.hZ]
  exact h

/-- Short-line limit of the exact shunt branch: `Y_sh(ℓ) = tanh(γℓ/2)/Z_c = (Y/2)ℓ + o(ℓ)`. -/
@[powerlib_foundation] theorem piShunt_shortLine :
    HasDerivAt (fun ℓ : ℂ => tanh (p.γ * ℓ / 2) / p.Zc) (p.Y / 2) 0 := by
  have hZc := p.Zc_ne
  have harg : HasDerivAt (fun ℓ : ℂ => p.γ * ℓ / 2) (p.γ / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul p.γ).div_const 2
  have hc0 : cosh (p.γ * 0 / 2) ≠ 0 := by simp
  have ht := ((Complex.hasDerivAt_sinh (p.γ * 0 / 2)).div (Complex.hasDerivAt_cosh (p.γ * 0 / 2))
    hc0).comp (0 : ℂ) harg
  have hfun : (fun ℓ : ℂ => tanh (p.γ * ℓ / 2) / p.Zc) =
      fun ℓ => ((sinh / cosh) ∘ fun ℓ : ℂ => p.γ * ℓ / 2) ℓ / p.Zc := by
    funext ℓ; simp [Complex.tanh_eq_sinh_div_cosh]
  rw [hfun]
  convert ht.div_const p.Zc using 1
  rw [p.hγ]
  simp
  field_simp

/-! ## Input impedance with a load -/

/-- Denominator of the input impedance, `Z_c cosh γℓ + Z_L sinh γℓ`. -/
def inputDen (ℓ ZL : ℂ) : ℂ := p.Zc * cosh (p.γ * ℓ) + ZL * sinh (p.γ * ℓ)

/-- Port relation with a load `V₂ = Z_L I₂`:
`V₁ (Z_c cosh γℓ + Z_L sinh γℓ) = Z_c (Z_L cosh γℓ + Z_c sinh γℓ) I₁`. -/
@[powerlib_foundation] theorem input_relation (ℓ ZL I₂ : ℂ) :
    (chain p ℓ *ᵥ ![ZL * I₂, I₂]) 0 * inputDen p ℓ ZL =
      p.Zc * (ZL * cosh (p.γ * ℓ) + p.Zc * sinh (p.γ * ℓ)) * (chain p ℓ *ᵥ ![ZL * I₂, I₂]) 1 := by
  have hinv : p.Zc * p.Zc⁻¹ = 1 := mul_inv_cancel₀ p.Zc_ne
  simp only [chain, inputDen, mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, div_eq_mul_inv]
  linear_combination (-(ZL * cosh (p.γ * ℓ) + p.Zc * sinh (p.γ * ℓ)) * sinh (p.γ * ℓ) * ZL * I₂) *
    hinv

/-- `Z_in = Z_c (Z_L + Z_c tanh γℓ)/(Z_c + Z_L tanh γℓ)` wherever both sides are defined. -/
@[powerlib_foundation] theorem inputImpedance_tanh (ℓ ZL : ℂ) (hc : cosh (p.γ * ℓ) ≠ 0) :
    p.Zc * (ZL * cosh (p.γ * ℓ) + p.Zc * sinh (p.γ * ℓ)) / inputDen p ℓ ZL =
      p.Zc * (ZL + p.Zc * tanh (p.γ * ℓ)) / (p.Zc + ZL * tanh (p.γ * ℓ)) := by
  simp only [inputDen, Complex.tanh_eq_sinh_div_cosh]
  rw [show ZL + p.Zc * (sinh (p.γ * ℓ) / cosh (p.γ * ℓ)) =
      (ZL * cosh (p.γ * ℓ) + p.Zc * sinh (p.γ * ℓ)) / cosh (p.γ * ℓ) by field_simp,
    show p.Zc + ZL * (sinh (p.γ * ℓ) / cosh (p.γ * ℓ)) =
      (p.Zc * cosh (p.γ * ℓ) + ZL * sinh (p.γ * ℓ)) / cosh (p.γ * ℓ) by field_simp,
    mul_div_assoc', div_div_div_cancel_right₀ hc]

/-- Correction: with a short-circuited far end (`Z_L = 0`) the poles of `Z_in` are exactly the
quarter-wave set `γℓ = (2k+1)πi/2`. -/
@[powerlib_foundation] theorem shorted_denominator_zero_iff (ℓ : ℂ) :
    inputDen p ℓ 0 = 0 ↔ ∃ k : ℤ, p.γ * ℓ = (2 * k + 1) * Real.pi / 2 * I := by
  simp only [inputDen, zero_mul, add_zero, mul_eq_zero, p.Zc_ne, false_or]
  rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k - 1, ?_⟩
    have : p.γ * ℓ = (p.γ * ℓ * I) * (-I) := by ring_nf; simp
    rw [this, hk]
    push_cast
    ring_nf
  · rintro ⟨k, hk⟩
    refine ⟨-k - 1, ?_⟩
    rw [hk]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring

/-- Lossless line, shorted far end: with `γ = iω/c` (`γℓ = iωτ`) the denominator vanishes iff
`ωτ = (2k+1)π/2`, i.e. at `f = (2k+1)/(4τ) = (2k+1)c/(4ℓ)`. -/
@[powerlib_foundation] theorem lossless_quarterWave (ω τ : ℝ) :
    cosh ((ω * τ : ℝ) * I) = 0 ↔ ∃ k : ℤ, ω * τ = (2 * k + 1) * Real.pi / 2 := by
  rw [Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.ofReal_eq_zero, Real.cos_eq_zero_iff]

/-- Correction: a matched load `Z_L = Z_c` produces no pole: the denominator is
`Z_c e^{γℓ} ≠ 0` and `V₁ = Z_c I₁` at every frequency. -/
@[powerlib_foundation] theorem matched_inputImpedance (ℓ I₂ : ℂ) :
    inputDen p ℓ p.Zc = p.Zc * exp (p.γ * ℓ) ∧
      (chain p ℓ *ᵥ ![p.Zc * I₂, I₂]) 0 = p.Zc * (chain p ℓ *ᵥ ![p.Zc * I₂, I₂]) 1 := by
  have hden : inputDen p ℓ p.Zc = p.Zc * exp (p.γ * ℓ) := by
    rw [inputDen, ← Complex.cosh_add_sinh]; ring
  refine ⟨hden, ?_⟩
  have h := input_relation p ℓ p.Zc I₂
  rw [hden] at h
  have hne : p.Zc * exp (p.γ * ℓ) ≠ 0 := mul_ne_zero p.Zc_ne (Complex.exp_ne_zero _)
  have e : p.Zc * (p.Zc * cosh (p.γ * ℓ) + p.Zc * sinh (p.γ * ℓ)) =
      p.Zc * (p.Zc * exp (p.γ * ℓ)) := by rw [← Complex.cosh_add_sinh]; ring
  rw [e] at h
  apply mul_right_cancel₀ hne
  linear_combination h

/-- Correction: `tanh` is not entire; it is not even continuous at `iπ/2`. -/
@[powerlib_foundation] theorem tanh_not_continuousAt :
    ¬ ContinuousAt Complex.tanh ((Real.pi / 2 : ℝ) * I) := by
  intro h
  set z₀ : ℂ := (Real.pi / 2 : ℝ) * I with hz₀
  have hcosh0 : cosh z₀ = 0 := by
    rw [hz₀, Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hsinh0 : sinh z₀ = I := by
    rw [hz₀, Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one,
      one_mul]
  have hmap : Filter.Tendsto (fun ε : ℝ => z₀ + ε) (nhdsWithin 0 {0}ᶜ) (nhds z₀) := by
    have : Continuous fun ε : ℝ => z₀ + ε := continuous_const.add Complex.continuous_ofReal
    have h0 := this.tendsto 0
    simp only [Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := (h.mul Complex.continuous_cosh.continuousAt).tendsto.comp hmap
  have h2 := (Complex.continuous_sinh.continuousAt (x := z₀)).tendsto.comp hmap
  have heq : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ,
      ((fun z => tanh z * cosh z) ∘ fun ε : ℝ => z₀ + ε) ε = (sinh ∘ fun ε : ℝ => z₀ + ε) ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hc : cosh (z₀ + ε) ≠ 0 := by
      rw [Complex.cosh_add, hcosh0, hsinh0, zero_mul, zero_add, ← Complex.ofReal_sinh]
      exact mul_ne_zero Complex.I_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr hε))
    simp only [Function.comp_apply, Complex.tanh_eq_sinh_div_cosh]
    field_simp
  have := tendsto_nhds_unique (h1.congr' heq) h2
  simp only [Pi.mul_apply, hcosh0, mul_zero, hsinh0] at this
  exact Complex.I_ne_zero this.symm

/-! ## Multi-conductor lines -/

/-- Correction for the matrix chain matrix: for `V' = -Z I`, `I' = -Y V` the voltage obeys
`V'' = ZY V` while the current obeys `I'' = YZ I`. -/
@[powerlib_foundation] theorem multiconductor_second_order {n : ℕ}
    (Z Y : Matrix (Fin n) (Fin n) ℂ) {V I : ℝ → Fin n → ℂ}
    (hV : ∀ x, HasDerivAt V (-(Z *ᵥ I x)) x) (hI : ∀ x, HasDerivAt I (-(Y *ᵥ V x)) x) (x : ℝ) :
    HasDerivAt (fun x => -(Z *ᵥ I x)) ((Z * Y) *ᵥ V x) x ∧
      HasDerivAt (fun x => -(Y *ᵥ V x)) ((Y * Z) *ᵥ I x) x := by
  let LZ : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    ((Matrix.toLin' Z).toContinuousLinearMap).restrictScalars ℝ
  let LY : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    ((Matrix.toLin' Y).toContinuousLinearMap).restrictScalars ℝ
  have hZ : ∀ v, LZ v = Z *ᵥ v := fun v => rfl
  have hY : ∀ v, LY v = Y *ᵥ v := fun v => rfl
  constructor
  · have h := (LZ.hasFDerivAt.comp_hasDerivAt x (hI x)).neg
    simp only [Function.comp_def, hZ] at h
    convert h using 1
    rw [mulVec_neg, neg_neg, mulVec_mulVec]
  · have h := (LY.hasFDerivAt.comp_hasDerivAt x (hV x)).neg
    simp only [Function.comp_def, hY] at h
    convert h using 1
    rw [mulVec_neg, neg_neg, mulVec_mulVec]

/-- `ZY ≠ YZ` in general (so the two diagonal chain blocks differ). -/
@[powerlib_foundation] theorem matrix_mul_not_comm_example :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 1, 1] ≠
      !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

/-! ## Limits of `Z_c(s)` and `γ(s)` with an explicit branch -/

/-- Characteristic impedance `Z_c(s) = ((R' + sL')/(G' + sC'))^{1/2}`, principal branch. -/
def ZcOf (L C R G : ℝ) (s : ℂ) : ℂ := ((R + s * L) / (G + s * C)) ^ ((2 : ℂ)⁻¹)

/-- Propagation constant on the same branch, `γ(s) = Z_c(s) (G' + sC')`
(so `γ² = (R' + sL')(G' + sC')`). -/
def gammaOf (L C R G : ℝ) (s : ℂ) : ℂ := ZcOf L C R G s * (G + s * C)

@[powerlib_foundation] theorem ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ^ ((2 : ℂ)⁻¹) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
  norm_num

/-- DC values on the principal branch: `Z_c(0) = √(R'/G')`, `γ(0) = √(R'G')`. -/
@[powerlib_foundation] theorem ZcOf_zero {L C R G : ℝ} (hR : 0 ≤ R) (hG : 0 < G) :
    ZcOf L C R G 0 = (Real.sqrt (R / G) : ℂ) ∧ gammaOf L C R G 0 = (Real.sqrt (R * G) : ℂ) := by
  have h1 : ZcOf L C R G 0 = (Real.sqrt (R / G) : ℂ) := by
    rw [ZcOf]
    simp only [zero_mul, add_zero]
    rw [← Complex.ofReal_div, ofReal_cpow_half (div_nonneg hR hG.le)]
  refine ⟨h1, ?_⟩
  rw [gammaOf, h1]
  simp only [zero_mul, add_zero]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [Real.sqrt_div' _ hG.le, div_mul_eq_mul_div, Real.sqrt_mul' _ hG.le]
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
  field_simp
  rw [Real.sq_sqrt hG.le]

@[powerlib_foundation] theorem ratio_tendsto {L C R G : ℝ} (hC : 0 < C) :
    Filter.Tendsto (fun s : ℂ => (R + s * L) / (G + s * C)) (Bornology.cobounded ℂ)
      (nhds ((L / C : ℝ) : ℂ)) := by
  have hC' : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hw : Filter.Tendsto (fun w : ℂ => (R * w + L) / (G * w + C)) (nhds 0)
      (nhds ((L / C : ℝ) : ℂ)) := by
    have hcont : ContinuousAt (fun w : ℂ => (R * w + L) / (G * w + C)) 0 := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · simpa using hC'
    have := hcont.tendsto
    simpa using this
  have hcomp := hw.comp Filter.tendsto_inv₀_cobounded
  apply hcomp.congr'
  filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with s hs
  simp only [Function.comp_apply]
  field_simp

/-- High-frequency limit on the principal branch: `Z_c(s) → √(L'/C')` as `|s| → ∞`. -/
@[powerlib_foundation] theorem ZcOf_tendsto {L C R G : ℝ} (hL : 0 < L) (hC : 0 < C) :
    Filter.Tendsto (ZcOf L C R G) (Bornology.cobounded ℂ) (nhds (Real.sqrt (L / C) : ℂ)) := by
  have hslit : ((L / C : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (div_pos hL hC)
  have hc := (continuousAt_cpow_const (b := (2 : ℂ)⁻¹) hslit).tendsto.comp (ratio_tendsto (R := R)
    (G := G) (L := L) hC)
  rw [ofReal_cpow_half (div_pos hL hC).le] at hc
  exact hc

/-- High-frequency limit of the propagation constant on the same branch:
`γ(s)/s → √(L'C')`. -/
@[powerlib_foundation] theorem gammaOf_div_tendsto {L C R G : ℝ} (hL : 0 < L) (hC : 0 < C) :
    Filter.Tendsto (fun s => gammaOf L C R G s / s) (Bornology.cobounded ℂ)
      (nhds (Real.sqrt (L * C) : ℂ)) := by
  have hlim : Filter.Tendsto (fun s : ℂ => ZcOf L C R G s * (G * s⁻¹ + C)) (Bornology.cobounded ℂ)
      (nhds ((Real.sqrt (L / C) : ℂ) * (G * 0 + C))) := by
    apply (ZcOf_tendsto hL hC).mul
    exact (((Filter.tendsto_inv₀_cobounded (α := ℂ)).const_mul (G : ℂ)).add_const (C : ℂ))
  have hval : (Real.sqrt (L / C) : ℂ) * (G * 0 + C) = (Real.sqrt (L * C) : ℂ) := by
    simp only [mul_zero, zero_add]
    rw [← Complex.ofReal_mul]
    congr 1
    rw [Real.sqrt_div' _ hC.le, Real.sqrt_mul' _ hC.le]
    have hs : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
    field_simp
    rw [Real.sq_sqrt hC.le]
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with s hs
  simp only [gammaOf]
  field_simp

end powerlib.Line.Phasor
