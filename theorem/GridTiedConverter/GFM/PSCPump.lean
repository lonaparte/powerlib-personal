import theorem.GridTiedConverter.GFM.VSMLPFAlgebra
import theorem.ParametricResonance.ElementDecomposition
import theorem.PhasePlane.Planar

/-! # PSC without active damping: modal damping, kinematic factor and the 2:1 pump coefficient

The power-synchronization loop with a power low-pass and no active damping (`r_a = 0`) under a
grid-angle modulation: its modal damping is exactly `σ_m = ω_f/2`, so `σ_m/Ω_m = ω_f/(2Ω_m)` cannot
approach zero; its first-order Floquet data (single modulated element, forced response, weights
of Table 4) and the closed form of the pump coefficient. The quasi-static equilibrium with a
high-pass active resistance is the same as without it.

Model boundary.
* State `x = (δ, p_f) : Dynamics.State 2` (converter angle relative to the grid frame, filtered
  power), grid angle `θ` as input, continuous time:
  `δ̇ = k (p* − p_f)`, `ṗ_f = ω_f (P(δ − θ) − p_f)` (`field`), with an arbitrary static power map
  `P(Ψ)` (quasi-static network), `K = P'(Ψ₀)`, `P₂ = P''(Ψ₀)`. No active damping branch, AVR,
  inner loops, current limiting, PLL, delay or PWM.
* Active-damping equilibrium: phasors, the converter voltage `u = E e^{jδ} − r_a (i − ℓ)` behind
  `R + jX` to the grid `V`, with the high-pass state `ℓ` at its steady state `ℓ = i`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (PSC core), §4.2 (`r_a = 0`: `σ_m/Ω_m = ω_f/(2Ω_m) = O(1)`),
Table 4 (PSC, `r_a = 0`: `w_{δp_f} = w_{p_fδ} = jΩ₀²/(2Ω_m)`, `w_{p_fp_f} = −ω_f λ_m/(2jΩ_m)`),
Table 6 (PSC: `S_m` with `K(j2Ω_m) = K_r`), Table 9, §9 item 8 (`ζ₀` definitions).

Results.
* `hasFDerivAt_field`, `hasDerivAt_field_input`, `charPoly` (`s² + ω_f s + k ω_f K`).
* `root_re` — every non-real characteristic root has real part `−ω_f/2`: `σ_m = ω_f/2` exactly.
* `jacAt_const`, `modulation_eq` — only `(p_f, δ)` is modulated (Lemma 1):
  `A₁ = ω_f P₂ (z_δ − 1) e_{p_f} e_δᵀ`.
* `forced_eq` — the forced response `z⁽¹⁾ = (kω_fK, −ω_fK s)/D(s)`; `sensitivity_eq` — `S = 1 − z_δ = s(s + ω_f)/D(s)`;
  `sensitivity_mode` — at `s = 2jΩ_m` with the roots `−ω_f/2 ± jΩ_m`,
  `S = (4 − 4jζ)/(3 − 4jζ − ζ²)`, `ζ = ω_f/(2Ω_m)`.
* `right_eig`, `left_eig`, `left_right`; `weight_01`, `weight_10`, `weight_11`
  (`−kω_fK/D'(λ)`, `−kω_fK/D'(λ)`, `−ω_fλ/D'(λ)`), and at `λ = −ω_f/2 + jΩ_m` (`D' = 2jΩ_m`)
  the Table 4 values (`weight_mode`).
* `pump_eq` — `g = ρ · w`, `ρ = (P₂/K)(z_δ − 1)`, `w = w_{p_f δ}`.
* `equilibrium_activeDamping` — with `ℓ = i` the active-damping current equals the current
  without active resistance: the high-pass `r_a` does not move the operating point.

Corrections.
* Table 6 gives `S_m = (4 − j4ζ₀)/(4 − K(j2Ω_m)/K_r − j4ζ₀)`, i.e. `(4 − 4jζ₀)/(3 − 4jζ₀)` without
  active damping. With `ζ = ω_f/(2Ω_m)` and the exact mode frequency the denominator is
  `3 − 4jζ − ζ²` (`sensitivity_mode`); the difference is the `O(ζ₀²)` term of item 8 of §9.

Family and connection conclusions.
None: static evidence on the PSC core (Jacobian, damping, forced response, eigentriple, pump
coefficient, equilibrium).
-/

noncomputable section
namespace powerlib.GFM
open powerlib.Dynamics (State)
open Complex ComplexConjugate Matrix

/-- Parameters of the PSC loop with a power low-pass and an arbitrary power map. -/
structure PSCCore where
  k : ℝ
  ωf : ℝ
  Pref : ℝ
  P : ℝ → ℝ

namespace PSCCore

variable (d : PSCCore)

/-- The PSC field with grid angle `θ`. -/
def field (θ : ℝ) (x : State 2) : State 2 :=
  PhasePlane.mk (d.k * (d.Pref - x 1)) (d.ωf * (d.P (x 0 - θ) - x 1))

/-- The Jacobian with synchronizing coefficient `K`. -/
def jacobian (K : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -d.k; d.ωf * K, -d.ωf]

/-- The input vector `B = ∂f/∂θ`. -/
def inputVec (K : ℝ) : Fin 2 → ℝ := ![0, -(d.ωf * K)]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field {θ K : ℝ} {x : State 2}
    (hP : HasDerivAt d.P K (x 0 - θ)) :
    HasFDerivAt (d.field θ) (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (d.jacobian K)) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · have h := ((hasFDerivAt_const d.Pref x).sub h1).const_mul d.k
    convert h using 1
    · funext y; simp [field, PhasePlane.mk]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, PhasePlane.toEuclideanCLM_apply_zero]
  · have hs := hP.comp_hasFDerivAt x (h0.sub_const θ)
    have h := (hs.sub h1).const_mul d.ωf
    convert h using 1
    · funext y; simp [field, PhasePlane.mk]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, PhasePlane.toEuclideanCLM_apply_one]
      ring

@[tmio M, powerlib_domain] theorem hasDerivAt_field_input {θ K : ℝ} {x : State 2}
    (hP : HasDerivAt d.P K (x 0 - θ)) (i : Fin 2) :
    HasDerivAt (fun θ => d.field θ x i) (d.inputVec K i) θ := by
  fin_cases i
  · simpa [field, inputVec, PhasePlane.mk] using hasDerivAt_const θ (d.k * (d.Pref - x 1))
  · have h1 : HasDerivAt (fun θ : ℝ => x 0 - θ) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub (x 0)
    have h := ((hP.comp θ h1).sub_const (x 1)).const_mul d.ωf
    convert h using 1
    · funext θ; simp [field, PhasePlane.mk]
    · simp [inputVec]

/-- `D(s) = s² + ω_f s + k ω_f K`. -/
def charPolyEval (K : ℝ) (s : ℂ) : ℂ := s ^ 2 + (d.ωf : ℂ) * s + ((d.k * d.ωf * K : ℝ) : ℂ)

@[tmio M, powerlib_domain] theorem charPoly (K : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (d.jacobian K) s).det = d.charPolyEval K s := by
  simp [Linear.characteristicMatrix, jacobian, charPolyEval, Matrix.det_fin_two]
  ring

/-- `σ_m = ω_f/2` exactly: every non-real characteristic root has real part `−ω_f/2`. -/
@[tmio M, powerlib_domain] theorem root_re {K : ℝ} {s : ℂ} (hroot : d.charPolyEval K s = 0)
    (him : s.im ≠ 0) : s.re = -(d.ωf / 2) := by
  refine VSMLPF.reduced_root_re (ω0sq := d.k * d.ωf * K) ?_ him
  simp only [charPolyEval] at hroot
  push_cast at hroot ⊢
  linear_combination hroot

/-! ## The modulation `A₁` -/

/-- The Jacobian at the point `(x, θ)`. -/
def jacAt (q : State 2 × ℝ) : Matrix (Fin 2) (Fin 2) ℝ := d.jacobian (deriv d.P (q.1 0 - q.2))

/-- Lemma 1: every entry except `(p_f, δ)` is constant. -/
@[tmio M, powerlib_domain] theorem jacAt_const {i k : Fin 2} (h : ¬ (i = 1 ∧ k = 0)) :
    ∃ c : ℝ, ∀ q, d.jacAt q i k = c := by
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;> simp [jacAt, jacobian]

/-- `A₁ = ω_f P₂ (z_δ − 1) e_{p_f} e_δᵀ`. -/
def modMatrix (P2 : ℝ) (z : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; (d.ωf * P2 : ℝ) * (z 0 - 1), 0]

@[tmio M, powerlib_domain] theorem modulation_eq {x : State 2} {θ P2 : ℝ}
    (hP2 : HasDerivAt (deriv d.P) P2 (x 0 - θ)) (z : Fin 2 → ℂ) :
    ParametricResonance.Element.modulation d.jacAt (x, θ)
        (WithLp.toLp 2 (fun i => (z i).re), 1) (WithLp.toLp 2 (fun i => (z i).im), 0) =
      d.modMatrix P2 z := by
  have hL := ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt.comp
    (x, θ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, θ)))).sub (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, θ)))
  have h10 := (hP2.comp_hasFDerivAt (x, θ) hL).const_mul d.ωf
  have e10 : HasFDerivAt (fun q : State 2 × ℝ => d.jacAt q 1 0) _ (x, θ) :=
    h10.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp [jacAt, jacobian])
  ext i k
  by_cases hik : i = 1 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := hik
    simp only [ParametricResonance.Element.modulation]
    rw [e10.fderiv]
    have hz0 := Complex.re_add_im (z 0)
    simp [modMatrix]
    conv_rhs => rw [← hz0]
    ring
  · obtain ⟨c, hc⟩ := d.jacAt_const hik
    rw [ParametricResonance.Element.modulation_eq_zero_of_const hc]
    fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> simp [modMatrix]

/-! ## Forced response and kinematic factor -/

/-- The forced response `z⁽¹⁾(s) = (kω_fK, −ω_fK s)/D(s)`. -/
def forced (K : ℝ) (s : ℂ) : Fin 2 → ℂ :=
  ![((d.k * d.ωf * K : ℝ) : ℂ) / d.charPolyEval K s, -((d.ωf * K : ℝ) : ℂ) * s / d.charPolyEval K s]

@[tmio M, powerlib_domain] theorem forced_eq (K : ℝ) {s : ℂ} (hD : d.charPolyEval K s ≠ 0) :
    Linear.characteristicMatrix (d.jacobian K) s *ᵥ d.forced K s =
      (fun i => ((d.inputVec K i : ℝ) : ℂ)) := by
  have hND : ((d.k * d.ωf * K : ℝ) : ℂ) + s * (s + d.ωf) = d.charPolyEval K s := by
    simp only [charPolyEval]; ring
  funext i
  fin_cases i
  · simp only [Linear.characteristicMatrix, jacobian, forced, mulVec, dotProduct,
      Fin.sum_univ_two]
    simp [inputVec]
    ring
  · simp only [Linear.characteristicMatrix, jacobian, forced, mulVec, dotProduct,
      Fin.sum_univ_two]
    simp [inputVec]
    calc _ = -((d.ωf : ℂ) * K) *
          ((((d.k * d.ωf * K : ℝ) : ℂ) + s * (s + d.ωf)) / d.charPolyEval K s) := by
          push_cast; ring
      _ = _ := by rw [hND, div_self hD]; ring

@[tmio M, powerlib_domain] theorem sensitivity_eq (K : ℝ) {s : ℂ} (hD : d.charPolyEval K s ≠ 0) :
    1 - d.forced K s 0 = s * (s + d.ωf) / d.charPolyEval K s := by
  simp only [forced, Matrix.cons_val_zero]
  field_simp
  simp only [charPolyEval]
  push_cast
  ring

/-- At `s = 2jΩ_m`, with roots `−ω_f/2 ± jΩ_m` (`k ω_f K = Ω_m² + ω_f²/4`):
`S = (4 − 4jζ)/(3 − 4jζ − ζ²)`, `ζ = ω_f/(2Ω_m)`. -/
@[tmio M, powerlib_domain] theorem sensitivity_mode {K Ω : ℝ} (hΩ : 0 < Ω)
    (hK : d.k * d.ωf * K = Ω ^ 2 + d.ωf ^ 2 / 4) (hD : d.charPolyEval K (2 * Ω * I) ≠ 0) :
    1 - d.forced K (2 * Ω * I) 0 =
      (4 - 4 * I * ((d.ωf / (2 * Ω) : ℝ) : ℂ)) /
        (3 - 4 * I * ((d.ωf / (2 * Ω) : ℝ) : ℂ) - ((d.ωf / (2 * Ω) : ℝ) : ℂ) ^ 2) := by
  rw [d.sensitivity_eq K hD]
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hD' := hD
  simp only [charPolyEval, hK] at hD' ⊢
  have hden : (3 : ℂ) - 4 * I * ((d.ωf / (2 * Ω) : ℝ) : ℂ) - ((d.ωf / (2 * Ω) : ℝ) : ℂ) ^ 2 ≠ 0 := by
    intro h
    apply hD'
    have e : (2 * (Ω : ℂ) * I) ^ 2 + (d.ωf : ℂ) * (2 * Ω * I) + ((Ω ^ 2 + d.ωf ^ 2 / 4 : ℝ) : ℂ) =
        -(Ω : ℂ) ^ 2 * (3 - 4 * I * ((d.ωf / (2 * Ω) : ℝ) : ℂ) - ((d.ωf / (2 * Ω) : ℝ) : ℂ) ^ 2) := by
      push_cast; field_simp; linear_combination (64 * (Ω : ℂ) ^ 2) * I_sq
    rw [e, h, mul_zero]
  rw [div_eq_div_iff hD' hden]
  push_cast
  field_simp
  linear_combination (-(2 * (Ω : ℂ) * d.ωf ^ 2) - 8 * Ω ^ 3) * I_sq

/-! ## The eigentriple and the pump coefficient -/

/-- `D'(λ) = 2λ + ω_f`. -/
def charPolyDeriv (s : ℂ) : ℂ := 2 * s + d.ωf

/-- Right eigenvector `(1, −λ/k)`. -/
def right (lam : ℂ) : Fin 2 → ℂ := ![1, -lam / d.k]

/-- Left eigenvector `c (ω_f K/λ, 1)`, `c = −k/D'(λ)`. -/
def left (K : ℝ) (lam : ℂ) : Fin 2 → ℂ :=
  ![-(d.k : ℂ) / d.charPolyDeriv lam * ((d.ωf * K : ℝ) / lam), -(d.k : ℂ) / d.charPolyDeriv lam]

@[tmio M, powerlib_domain] theorem right_eig {K : ℝ} {lam : ℂ} (hk : d.k ≠ 0)
    (hroot : d.charPolyEval K lam = 0) :
    Linear.complexify (d.jacobian K) *ᵥ d.right lam = lam • d.right lam := by
  have hk' : (d.k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [charPolyEval] at hroot
  push_cast at hroot
  funext i
  fin_cases i
  · simp [Linear.complexify, jacobian, right, mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  · simp [Linear.complexify, jacobian, right, mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination hroot

@[tmio M, powerlib_domain] theorem left_eig {K : ℝ} {lam : ℂ} (hlam : lam ≠ 0)
    (hroot : d.charPolyEval K lam = 0) :
    vecMul (d.left K lam) (Linear.complexify (d.jacobian K)) = lam • d.left K lam := by
  simp only [charPolyEval] at hroot
  push_cast at hroot
  simp only [left]
  generalize -(d.k : ℂ) / d.charPolyDeriv lam = c
  funext i
  fin_cases i
  · simp [Linear.complexify, jacobian, vecMul, dotProduct, Fin.sum_univ_two]
    field_simp
  · simp [Linear.complexify, jacobian, vecMul, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination (-c) * hroot

@[tmio M, powerlib_domain] theorem left_right {K : ℝ} {lam : ℂ} (hk : d.k ≠ 0) (hlam : lam ≠ 0)
    (hroot : d.charPolyEval K lam = 0) (hD' : d.charPolyDeriv lam ≠ 0) :
    d.left K lam ⬝ᵥ d.right lam = 1 := by
  have hk' : (d.k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [charPolyEval] at hroot
  push_cast at hroot
  simp only [left, right, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  field_simp
  simp only [charPolyDeriv]
  linear_combination (-1 : ℂ) * hroot

@[tmio M, powerlib_domain] theorem weight_01 (K : ℝ) (lam : ℂ) (hk : d.k ≠ 0) (hlam : lam ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K)) (d.left K lam)
        (d.right lam) 0 1 = -((d.k * d.ωf * K : ℝ) : ℂ) / d.charPolyDeriv lam := by
  have hk' : (d.k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp [ParametricResonance.Element.weight, Linear.complexify, jacobian, left, right]
  field_simp

@[tmio M, powerlib_domain] theorem weight_10 (K : ℝ) (lam : ℂ) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K)) (d.left K lam)
        (d.right lam) 1 0 = -((d.k * d.ωf * K : ℝ) : ℂ) / d.charPolyDeriv lam := by
  simp [ParametricResonance.Element.weight, Linear.complexify, jacobian, left, right]
  ring

@[tmio M, powerlib_domain] theorem weight_11 (K : ℝ) (lam : ℂ) (hk : d.k ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K)) (d.left K lam)
        (d.right lam) 1 1 = -(d.ωf : ℂ) * lam / d.charPolyDeriv lam := by
  have hk' : (d.k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp [ParametricResonance.Element.weight, Linear.complexify, jacobian, left, right]
  field_simp

/-- Table 4 (PSC, `r_a = 0`): at `λ = −ω_f/2 + jΩ_m`, `D'(λ) = 2jΩ_m`, so the loop weight is
`jΩ₀²/(2Ω_m)` with `Ω₀² = k ω_f K`. -/
@[tmio M, powerlib_domain] theorem weight_mode {K Ω : ℝ} (hΩ : Ω ≠ 0) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K))
        (d.left K (-(d.ωf / 2 : ℝ) + Ω * I)) (d.right (-(d.ωf / 2 : ℝ) + Ω * I)) 1 0 =
      I * ((d.k * d.ωf * K : ℝ) : ℂ) / (2 * Ω) := by
  rw [weight_10]
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  simp only [charPolyDeriv]
  push_cast
  field_simp
  linear_combination (-(2 * (Ω : ℂ)) * (d.k * d.ωf * K)) * I_sq

/-- `g = ρ · w`, `ρ = (P₂/K)(z_δ − 1)`, `w = w_{p_f δ}`. -/
@[tmio M, powerlib_domain] theorem pump_eq {K P2 : ℝ} (hK : K ≠ 0) (hωf : d.ωf ≠ 0)
    (z : Fin 2 → ℂ) (lam : ℂ) :
    ParametricResonance.Element.pump (d.modMatrix P2 z) (d.left K lam) (d.right lam) =
      ((P2 / K : ℝ) * (z 0 - 1)) * (-((d.k * d.ωf * K : ℝ) : ℂ) / d.charPolyDeriv lam) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hωf' : (d.ωf : ℂ) ≠ 0 := by exact_mod_cast hωf
  simp [ParametricResonance.Element.pump, modMatrix, left, right, mulVec, dotProduct,
    Fin.sum_univ_two]
  field_simp

/-! ## Equilibrium with a high-pass active resistance -/

/-- With the high-pass state at its steady state `ℓ = i`, the active-damping current
`(E e^{jδ} + r_a ℓ − V)/(R + r_a + jX)` is the current `(E e^{jδ} − V)/(R + jX)` without active
resistance: `r_a` does not change the operating point. -/
@[tmio M, powerlib_domain] theorem equilibrium_activeDamping {E V δ R X ra : ℝ} {i : ℂ}
    (hZ : (R : ℂ) + X * I ≠ 0) (hZa : (R : ℂ) + ra + X * I ≠ 0)
    (hi : i = ((E : ℂ) * exp (δ * I) + ra * i - V) / ((R : ℂ) + ra + X * I)) :
    i = ((E : ℂ) * exp (δ * I) - V) / ((R : ℂ) + X * I) := by
  rw [eq_div_iff hZa] at hi
  rw [eq_div_iff hZ]
  linear_combination hi

end PSCCore

end powerlib.GFM
