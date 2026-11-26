import theorem.Periodic.MeanTrace
import theorem.ParametricResonance.ResonantNormalForm
import theorem.Criteria.Hurwitz2
import theorem.Periodic.RobustThreshold

/-! # Combination resonance: frequency locking fails from four states on

For two states a parametric instability is frequency locked: with negative mean trace every
Floquet multiplier on or outside the unit circle is real (`det M = e^{∫ tr A} < 1`,
`Periodic.im_eq_zero_of_integral_trace_neg`), the unstable mode satisfies `x(t + T) = r x(t)` and
its spectrum lies on the lattice `(k/2)Ω`, `Ω = 2π/T` (`Periodic.real_mode_coeff`). This module
shows that the locking is a two-state accident. Two copies of a two-state system `ẋ = A(t) x`,
rotated against each other at the rate `ω`, form the four-state system

  `ẋ = (A(t) ⊗ I + ω I ⊗ J) x`,

the real form of `ż = (A(t) + iω) z` on `ℂ²`. The two terms commute, so
`Φ₄(t, s) = Φ(t, s) ⊗ R(ω(t − s))` and the multipliers are `e^{±iωT} μ`, `μ` a multiplier of
`ẋ = A(t) x`. Hence the mean trace stays negative (`tr (A ⊗ I + ω I ⊗ J) = 2 tr A`), the frozen
eigenvalues `λ(A(t)) ± iω` and the averaged eigenvalues `λ(Ā) ± iω` keep their real parts, a
Floquet instability of `ẋ = A(t) x` persists, and for `sin(ωT) ≠ 0` every multiplier on or
outside the unit circle is non-real. The frozen natural frequencies of the four-state system are
`ν ± ω` (`ν` that of `A`), and a pump near `2ν = (ν + ω) + (ν − ω)` is a sum-type combination
resonance; the unstable mode has the Floquet frequencies `(arg μ ± ωT + 2πk)/T`
(`ParametricResonance.Signature.floquet_factor`), off the locked lattice. A decoupled Hurwitz block
extends the example to every dimension `n ≥ 4`.

An exact instance is the 2:1 normal form `ż = (−σ + iΩ) z + c e^{2iΩt} z̄` of
`theorem/ParametricResonance/ResonantNormalForm.lean` (continuous coefficients, real unstable
multiplier `< −1`: the half-frequency resonance), with `σ > 0` and `σ² < |c|² < σ² + Ω²`: its
frozen matrices are Hurwitz, its average is `[[−σ, −Ω], [Ω, −σ]]`, and it is Floquet unstable.
The square-wave Meissner example of `theorem/ParametricResonance/Meissner.lean` has discontinuous
coefficients and is not a system of the continuous Floquet theory used here, so it is not used.

Consequence for the separation of small-signal and parametric instability: in `n ≥ 4` states the
real-multiplier (frequency) signature does not identify a parametric instability; what still
separates the classes is the mean trace (`theorem/Periodic/MeanTrace.lean`: a positive mean trace
is unstable at every level), the robust threshold `b ≥ α/K` (`theorem/Periodic/RobustThreshold.lean`)
and the limit of small modulation (`theorem/Periodic/Persistence.lean`).

Scope.
* `ẋ = A(t) x` on `ℝ^X` (finite `X`; `X = Fin 2` for the locking statements) with a continuous
  real `T`-periodic `A`, `T > 0`; the rotated system lives on `ℝ^{X × Fin 2}` (`X × Fin 2 ≃ Fin 4`
  for `X = Fin 2`, relabelled by `finProdFinEquiv` where `LinearSystems.IsHurwitz` is stated); the
  padded system on `(X × Fin 2) ⊕ Fin k`. `J = NormalForm.quarter`, `R(θ) = NormalForm.rot θ`.
* Transition and monodromy matrices of `theorem/Periodic/Transition.lean`; multipliers are the
  complex spectrum of the complexified monodromy; Hurwitz stability on a general finite index is
  `Linear.SpectrallyStable`; averages are written `∫₀ᵀ A = T • Ā`.
* Generic mathematics; no model family.

Source: combination (sum-type) parametric resonance of multi-degree-of-freedom systems
(Nayfeh–Mook, *Nonlinear Oscillations*, 1979, Ch. 5, parametrically excited systems;
Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*, combination
resonances); the realification of a complex
matrix (`ℂ^X ≅ ℝ^{X × 2}`, `P + iQ ↦ P ⊗ I + Q ⊗ J`); the two-state locking results of
`theorem/Periodic/MeanTrace.lean`; the normal form of
`theorem/ParametricResonance/ResonantNormalForm.lean` (`floquetUnstable_nf_of_lt`).

Results.
* `kronOne`, `kronQuarter`, `realify` — the real form `P ⊗ I + Q ⊗ J` of `P + iQ`;
  `realify_mul`, `realify_smul`, `realify_one_zero`, `realify_mulVec`, `kronecker_rot`,
  `trace_realify` (`= 2 tr P`).
* `mem_spectrum_realify_iff` — `σ(P ⊗ I + Q ⊗ J) = σ(P + iQ) ∪ σ(P − iQ)`;
  `mem_spectrum_smul_iff`, `mem_spectrum_add_smul_one_iff`, `spectrallyStable_iff_forall_spectrum`.
* `transition_realify`, `monodromy_realify` — `Φ₄(t, s) = Φ(t, s) ⊗ R(ω(t − s))`, `M₄ = M ⊗ R(ωT)`;
  `mem_spectrum_monodromy_realify_iff` — the multipliers are `e^{±iωT} μ`.
* `spectrallyStable_realify_iff` — the frozen (and averaged) matrix `P ⊗ I + ω I ⊗ J` is Hurwitz
  iff `P` is; `integral_realify` — its average; `integral_trace_realify` — twice the mean trace.
* `unlocked` — two states, negative mean trace, Floquet unstable, `sin(ωT) ≠ 0`: the rotated
  four-state system has negative mean trace, is Floquet unstable, and every multiplier with
  `|λ| ≥ 1` is non-real.
* `nf_frozen_isHurwitz`, `integral_nfMatrix`, `combination_resonance` — the exact four-state
  instance: Hurwitz frozen and averaged matrices (on `Fin 4`), negative mean trace, Floquet
  unstable, all unstable multipliers non-real.
* `blockLeft`, `blockRight`, `transition_fromBlocks`, `mem_spectrum_fromBlocks_iff`,
  `trace_fromBlocks_zero`, `unlocked_of_card` — appending a constant Hurwitz block on `k` states
  keeps all conclusions: frequency locking fails in every dimension `4 + k`.
-/

noncomputable section
namespace powerlib.Periodic.Combination

open Set Matrix Function Complex
open scoped Matrix.Norms.Operator Kronecker
open powerlib.Periodic
open powerlib.ParametricResonance.NormalForm (quarter rot nfMatrix pumpRe pumpIm)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The real form of a complex matrix -/

/-- `P ↦ P ⊗ I₂`. -/
def kronOne : Matrix X X ℝ →ₗ[ℝ] Matrix (X × Fin 2) (X × Fin 2) ℝ where
  toFun P := P ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
  map_add' P P' := add_kronecker P P' 1
  map_smul' c P := smul_kronecker c P 1

/-- `Q ↦ Q ⊗ J` with the quarter turn `J`. -/
def kronQuarter : Matrix X X ℝ →ₗ[ℝ] Matrix (X × Fin 2) (X × Fin 2) ℝ where
  toFun Q := Q ⊗ₖ quarter
  map_add' Q Q' := add_kronecker Q Q' quarter
  map_smul' c Q := smul_kronecker c Q quarter

/-- The real form `P ⊗ I + Q ⊗ J` of the complex matrix `P + iQ` acting on `ℂ^X ≅ ℝ^{X × 2}`
(`z = x₀ + i x₁ ↦ (x₀, x₁)`). -/
def realify (P Q : Matrix X X ℝ) : Matrix (X × Fin 2) (X × Fin 2) ℝ := kronOne P + kronQuarter Q

@[tmio T, powerlib_foundation] private theorem quarter_mul_quarter :
    quarter * quarter = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quarter, Matrix.mul_apply, Fin.sum_univ_two]

/-- Realified matrices multiply like complex matrices:
`(P + iQ)(P' + iQ') = (PP' − QQ') + i(PQ' + QP')`. -/
@[tmio T, powerlib_foundation] theorem realify_mul (P Q P' Q' : Matrix X X ℝ) :
    realify P Q * realify P' Q' = realify (P * P' - Q * Q') (P * Q' + Q * P') := by
  have h1 : ∀ A B : Matrix X X ℝ, kronOne A * kronOne B = kronOne (A * B) := fun A B => by
    simp only [kronOne, LinearMap.coe_mk, AddHom.coe_mk, ← mul_kronecker_mul, Matrix.mul_one]
  have h2 : ∀ A B : Matrix X X ℝ, kronOne A * kronQuarter B = kronQuarter (A * B) := fun A B => by
    simp only [kronOne, kronQuarter, LinearMap.coe_mk, AddHom.coe_mk, ← mul_kronecker_mul,
      Matrix.one_mul]
  have h3 : ∀ A B : Matrix X X ℝ, kronQuarter A * kronOne B = kronQuarter (A * B) := fun A B => by
    simp only [kronOne, kronQuarter, LinearMap.coe_mk, AddHom.coe_mk, ← mul_kronecker_mul,
      Matrix.mul_one]
  have h4 : ∀ A B : Matrix X X ℝ, kronQuarter A * kronQuarter B = -kronOne (A * B) := fun A B => by
    simp only [kronOne, kronQuarter, LinearMap.coe_mk, AddHom.coe_mk, ← mul_kronecker_mul,
      quarter_mul_quarter]
    ext ⟨i, k⟩ ⟨j, l⟩
    simp
  simp only [realify, add_mul, mul_add, h1, h2, h3, h4, map_sub, map_add]
  abel

omit [Fintype X] [DecidableEq X] in
/-- The real form is linear: `realify (a P) (a Q) = a realify P Q`. -/
@[tmio T, powerlib_foundation] theorem realify_smul (a : ℝ) (P Q : Matrix X X ℝ) :
    realify (a • P) (a • Q) = a • realify P Q := by
  simp only [realify, map_smul, smul_add]

omit [Fintype X] in
@[tmio T, powerlib_foundation] theorem realify_one_zero : realify (1 : Matrix X X ℝ) 0 = 1 := by
  simp [realify, kronOne]

omit [DecidableEq X] in
/-- Entries of the complexified real form acting on `w`: with `w₀ = w(·, 0)`, `w₁ = w(·, 1)`,
`(N w)(·, 0) = P w₀ − Q w₁` and `(N w)(·, 1) = P w₁ + Q w₀`. -/
@[tmio T, powerlib_foundation] theorem realify_mulVec (P Q : Matrix X X ℝ) (w : X × Fin 2 → ℂ)
    (i : X) :
    ((realify P Q).map (algebraMap ℝ ℂ) *ᵥ w) (i, 0) =
        (P.map (algebraMap ℝ ℂ) *ᵥ fun j => w (j, 0)) i -
          (Q.map (algebraMap ℝ ℂ) *ᵥ fun j => w (j, 1)) i ∧
      ((realify P Q).map (algebraMap ℝ ℂ) *ᵥ w) (i, 1) =
        (P.map (algebraMap ℝ ℂ) *ᵥ fun j => w (j, 1)) i +
          (Q.map (algebraMap ℝ ℂ) *ᵥ fun j => w (j, 0)) i := by
  simp only [realify, kronOne, kronQuarter, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.map_apply, Matrix.add_apply, kroneckerMap_apply,
    quarter, Matrix.one_apply]
  constructor
  · simp only [Fin.isValue, ↓reduceIte, mul_one]
    simp [← sub_eq_add_neg, Finset.sum_sub_distrib]
  · simp [Finset.sum_add_distrib, add_comm]

/-- **Spectrum of a real form.** The eigenvalues of `P ⊗ I + Q ⊗ J` are those of `P + iQ` together
with those of `P − iQ` (for an eigenvector `w`, `w₀ + i w₁` and `w₀ − i w₁` are eigenvectors of
`P + iQ` and `P − iQ`; conversely `v ↦ (v, ∓i v)`). -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_realify_iff (P Q : Matrix X X ℝ) (lam : ℂ) :
    lam ∈ spectrum ℂ ((realify P Q).map (algebraMap ℝ ℂ)) ↔
      lam ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ) + I • Q.map (algebraMap ℝ ℂ)) ∨
        lam ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ) - I • Q.map (algebraMap ℝ ℂ)) := by
  simp only [LTI.mem_spectrum_iff_exists_eigvec]
  set Pc := P.map (algebraMap ℝ ℂ) with hPc
  set Qc := Q.map (algebraMap ℝ ℂ) with hQc
  constructor
  · rintro ⟨w, hw, hNw⟩
    set w₀ : X → ℂ := fun j => w (j, 0) with hw₀
    set w₁ : X → ℂ := fun j => w (j, 1) with hw₁
    have e0 : ∀ i, (Pc *ᵥ w₀) i - (Qc *ᵥ w₁) i = lam * w₀ i := fun i => by
      rw [← (realify_mulVec P Q w i).1, hNw]; rfl
    have e1 : ∀ i, (Pc *ᵥ w₁) i + (Qc *ᵥ w₀) i = lam * w₁ i := fun i => by
      rw [← (realify_mulVec P Q w i).2, hNw]; rfl
    by_cases hp : w₀ + I • w₁ = 0
    · right
      refine ⟨w₀ - I • w₁, fun hq => hw ?_, ?_⟩
      · have h0 : ∀ j, w₀ j = 0 ∧ w₁ j = 0 := fun j => by
          have h1 := congrFun hp j
          have h2 := congrFun hq j
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
          have ha : w₀ j = 0 := by linear_combination (h1 + h2) / 2
          refine ⟨ha, ?_⟩
          have hb : I * w₁ j = 0 := by linear_combination (h1 - h2) / 2
          exact (mul_eq_zero.mp hb).resolve_left I_ne_zero
        funext ⟨j, k⟩
        fin_cases k
        · exact (h0 j).1
        · exact (h0 j).2
      · funext i
        simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination e0 i - I * e1 i + (Qc *ᵥ w₁) i * I_sq
    · left
      refine ⟨w₀ + I • w₁, hp, ?_⟩
      funext i
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0 i + I * e1 i + (Qc *ᵥ w₁) i * I_sq
  · rintro (⟨v, hv, hPv⟩ | ⟨v, hv, hPv⟩)
    · have hP' : ∀ i, (Pc *ᵥ v) i + I * (Qc *ᵥ v) i = lam * v i := fun i => by
        have := congrFun hPv i
        simpa [Matrix.add_mulVec, Matrix.smul_mulVec] using this
      set w : X × Fin 2 → ℂ := fun x => ![v x.1, ((-I) • v) x.1] x.2 with hw
      have hw0 : (fun j => w (j, 0)) = v := by funext j; simp [hw]
      have hw1 : (fun j => w (j, 1)) = (-I) • v := by funext j; simp [hw]
      refine ⟨w, fun h => hv ?_, ?_⟩
      · rw [← hw0, h]; rfl
      · funext ⟨i, k⟩
        fin_cases k
        · show ((realify P Q).map (algebraMap ℝ ℂ) *ᵥ w) (i, 0) = (lam • w) (i, 0)
          rw [(realify_mulVec P Q w i).1, hw0, hw1, Matrix.mulVec_smul]
          simp only [Pi.smul_apply, smul_eq_mul, hw, Fin.isValue, Matrix.cons_val_zero]
          linear_combination hP' i
        · show ((realify P Q).map (algebraMap ℝ ℂ) *ᵥ w) (i, 1) = (lam • w) (i, 1)
          rw [(realify_mulVec P Q w i).2, hw0, hw1, Matrix.mulVec_smul]
          simp only [Pi.smul_apply, smul_eq_mul, hw, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          linear_combination (-I) * hP' i + (Q.map (algebraMap ℝ ℂ) *ᵥ v) i * I_sq
    · have hP' : ∀ i, (Pc *ᵥ v) i - I * (Qc *ᵥ v) i = lam * v i := fun i => by
        have := congrFun hPv i
        simpa [Matrix.sub_mulVec, Matrix.smul_mulVec] using this
      set w : X × Fin 2 → ℂ := fun x => ![v x.1, (I • v) x.1] x.2 with hw
      have hw0 : (fun j => w (j, 0)) = v := by funext j; simp [hw]
      have hw1 : (fun j => w (j, 1)) = I • v := by funext j; simp [hw]
      refine ⟨w, fun h => hv ?_, ?_⟩
      · rw [← hw0, h]; rfl
      · funext ⟨i, k⟩
        fin_cases k
        · show ((realify P Q).map (algebraMap ℝ ℂ) *ᵥ w) (i, 0) = (lam • w) (i, 0)
          rw [(realify_mulVec P Q w i).1, hw0, hw1, Matrix.mulVec_smul]
          simp only [Pi.smul_apply, smul_eq_mul, hw, Fin.isValue, Matrix.cons_val_zero]
          linear_combination hP' i
        · show ((realify P Q).map (algebraMap ℝ ℂ) *ᵥ w) (i, 1) = (lam • w) (i, 1)
          rw [(realify_mulVec P Q w i).2, hw0, hw1, Matrix.mulVec_smul]
          simp only [Pi.smul_apply, smul_eq_mul, hw, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          linear_combination I * hP' i + (Q.map (algebraMap ℝ ℂ) *ᵥ v) i * I_sq

omit [Fintype X] [DecidableEq X] in
/-- The Kronecker product with a rotation is a real form: `P ⊗ R(θ) = realify (cos θ P) (sin θ P)`. -/
@[tmio T, powerlib_foundation] theorem kronecker_rot (P : Matrix X X ℝ) (θ : ℝ) :
    P ⊗ₖ rot θ = realify (Real.cos θ • P) (Real.sin θ • P) := by
  simp only [rot, realify, kronOne, kronQuarter, LinearMap.coe_mk, AddHom.coe_mk, kronecker_add,
    kronecker_smul, smul_kronecker]

omit [DecidableEq X] in
/-- `tr (P ⊗ I + Q ⊗ J) = 2 tr P`. -/
@[tmio T, powerlib_foundation] theorem trace_realify (P Q : Matrix X X ℝ) :
    (realify P Q).trace = 2 * P.trace := by
  have hJ : quarter.trace = 0 := by simp [quarter, Matrix.trace_fin_two]
  simp only [realify, kronOne, kronQuarter, LinearMap.coe_mk, AddHom.coe_mk, trace_add,
    trace_kronecker, hJ, mul_zero, add_zero, trace_one, Fintype.card_fin]
  push_cast
  ring

/-! ## The rotated system -/

section Rotated

variable {A : ℝ → Matrix X X ℝ}

/-- **Transition matrix of the rotated system.** For a continuous `T`-periodic `A`,
`ẋ = (A(t) ⊗ I + ω I ⊗ J) x`, the real form of `ż = (A(t) + iω) z` (two copies of `ẋ = A(t) x`
coupled by a rotation that commutes with it), has `Φ₄(t, s) = Φ(t, s) ⊗ R(ω (t − s))` for
`s ≤ t`. -/
@[tmio T, powerlib_foundation] theorem transition_realify (hA : Continuous A) {T : ℝ}
    (hP : Periodic A T) (hT : 0 < T) (ω : ℝ) {s t : ℝ} (hst : s ≤ t) :
    transition (fun r => realify (A r) (ω • 1)) t s = transition A t s ⊗ₖ rot (ω * (t - s)) := by
  set L₁ := LinearMap.toContinuousLinearMap (kronOne (X := X)) with hL₁
  set L₂ := LinearMap.toContinuousLinearMap (kronQuarter (X := X)) with hL₂
  have hreal : ∀ P Q : Matrix X X ℝ, realify P Q = L₁ P + L₂ Q := fun _ _ => rfl
  have hA₄c : Continuous fun r => realify (A r) (ω • 1) := by
    simp only [hreal]; exact (L₁.continuous.comp hA).add continuous_const
  obtain ⟨M₄, hM₄⟩ := exists_bound_of_periodic hA₄c (fun r => by simp only [hP r]) hT
  set Y : ℝ → Matrix (X × Fin 2) (X × Fin 2) ℝ := fun r =>
    realify (Real.cos (ω * (r - s)) • transition A r s) (Real.sin (ω * (r - s)) • transition A r s)
    with hY
  have hderiv : ∀ r, HasDerivAt Y (realify (A r) (ω • 1) * Y r) r := by
    intro r
    have hθ : HasDerivAt (fun r => ω * (r - s)) ω r := by
      simpa using ((hasDerivAt_id r).sub_const s).const_mul ω
    have hc := (Real.hasDerivAt_cos (ω * (r - s))).comp r hθ
    have hs := (Real.hasDerivAt_sin (ω * (r - s))).comp r hθ
    have hΦ := Dynamics.stm_hasDerivAt hA r s
    have h1 := hc.smul hΦ
    have h2 := hs.smul hΦ
    have h := (L₁.hasFDerivAt.comp_hasDerivAt r h1).add (L₂.hasFDerivAt.comp_hasDerivAt r h2)
    refine h.congr_deriv ?_
    rw [hY, realify_mul]
    simp only [hreal]
    congr 1 <;> congr 1 <;>
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Function.comp_apply, smul_smul]
    all_goals module
  have hcurve : IsIntegralCurveOn Y (matField fun r => realify (A r) (ω • 1)) (Ici s) :=
    fun r _ => (hderiv r).hasDerivWithinAt
  have h := transition_unique hA₄c hM₄ hcurve t hst
  have hYs : Y s = 1 := by
    simp [hY, LinearSystems.stateTransitionMatrix_self, realify_one_zero]
  rw [hYs, Matrix.mul_one] at h
  rw [← h, hY, kronecker_rot]

/-- The monodromy matrix of the rotated system is `M ⊗ R(ωT)`. -/
@[tmio T, powerlib_foundation] theorem monodromy_realify (hA : Continuous A) {T : ℝ}
    (hP : Periodic A T) (hT : 0 < T) (ω : ℝ) :
    monodromy (fun r => realify (A r) (ω • 1)) T 0 = monodromy A T 0 ⊗ₖ rot (ω * T) := by
  simp only [monodromy]
  rw [transition_realify hA hP hT ω (by linarith), zero_add, sub_zero]

/-- Eigenvalues of a nonzero multiple: `λ ∈ σ(c N) ↔ λ = c μ` for some `μ ∈ σ(N)`. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_smul_iff {N : Matrix X X ℂ} {c : ℂ}
    (hc : c ≠ 0) (lam : ℂ) : lam ∈ spectrum ℂ (c • N) ↔ ∃ μ ∈ spectrum ℂ N, lam = c * μ := by
  have h := spectrum.unit_smul_eq_smul (R := ℂ) N (Units.mk0 c hc)
  rw [Units.smul_def, Units.val_mk0] at h
  rw [h, Set.mem_smul_set]
  constructor
  · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, hμ, by rw [Units.smul_def, Units.val_mk0, smul_eq_mul]⟩
  · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, hμ, by rw [Units.smul_def, Units.val_mk0, smul_eq_mul]⟩

/-- **The multipliers of the rotated system** are `e^{±iωT} μ`, `μ` a multiplier of
`ẋ = A(t) x`. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_monodromy_realify_iff (hA : Continuous A)
    {T : ℝ} (hP : Periodic A T) (hT : 0 < T) (ω : ℝ) (lam : ℂ) :
    lam ∈ spectrum ℂ ((monodromy (fun r => realify (A r) (ω • 1)) T 0).map (algebraMap ℝ ℂ)) ↔
      ∃ μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)),
        lam = Complex.exp ((ω * T : ℝ) * I) * μ ∨ lam = Complex.exp (-((ω * T : ℝ) * I)) * μ := by
  have ep : (Real.cos (ω * T) • monodromy A T 0).map (algebraMap ℝ ℂ) +
      I • (Real.sin (ω * T) • monodromy A T 0).map (algebraMap ℝ ℂ) =
        Complex.exp ((ω * T : ℝ) * I) • (monodromy A T 0).map (algebraMap ℝ ℂ) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ext i j
    simp [Matrix.map_apply]
    ring
  have em : (Real.cos (ω * T) • monodromy A T 0).map (algebraMap ℝ ℂ) -
      I • (Real.sin (ω * T) • monodromy A T 0).map (algebraMap ℝ ℂ) =
        Complex.exp (-((ω * T : ℝ) * I)) • (monodromy A T 0).map (algebraMap ℝ ℂ) := by
    rw [show -(((ω * T : ℝ) : ℂ) * I) = ((-(ω * T) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    ext i j
    simp [Matrix.map_apply]
    ring
  rw [monodromy_realify hA hP hT ω, kronecker_rot, mem_spectrum_realify_iff, ep, em,
    mem_spectrum_smul_iff (Complex.exp_ne_zero _), mem_spectrum_smul_iff (Complex.exp_ne_zero _)]
  constructor
  · rintro (⟨μ, hμ, h⟩ | ⟨μ, hμ, h⟩)
    · exact ⟨μ, hμ, Or.inl h⟩
    · exact ⟨μ, hμ, Or.inr h⟩
  · rintro ⟨μ, hμ, h | h⟩
    · exact Or.inl ⟨μ, hμ, h⟩
    · exact Or.inr ⟨μ, hμ, h⟩

end Rotated

/-! ## Frozen, averaged and mean-trace data of the rotated system -/

section Data

/-- Spectral (Hurwitz) stability on a finite index is a condition on the complex spectrum. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_iff_forall_spectrum {ι : Type*}
    [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℝ) :
    Linear.SpectrallyStable N ↔ ∀ lam ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)), lam.re < 0 := by
  unfold Linear.SpectrallyStable
  refine forall_congr' fun s => ?_
  rw [Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair,
    ← LTI.mem_spectrum_iff_exists_eigvec]

/-- A shift by a multiple of the identity shifts the spectrum. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_add_smul_one_iff {N : Matrix X X ℂ} (c lam : ℂ) :
    lam ∈ spectrum ℂ (N + c • 1) ↔ lam - c ∈ spectrum ℂ N := by
  simp only [LTI.mem_spectrum_iff_exists_eigvec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_smul]
  constructor
  · rintro ⟨v, hv, h⟩; exact ⟨v, hv, by rw [← h]; abel⟩
  · rintro ⟨v, hv, h⟩; exact ⟨v, hv, by rw [h]; abel⟩

/-- **Frozen matrices of the rotated system.** `P ⊗ I + ω I ⊗ J` has the eigenvalues `λ ± iω`,
`λ` an eigenvalue of `P`; it is Hurwitz exactly when `P` is. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_iff (P : Matrix X X ℝ) (ω : ℝ) :
    Linear.SpectrallyStable (realify P (ω • 1)) ↔ Linear.SpectrallyStable P := by
  have e : (ω • (1 : Matrix X X ℝ)).map (algebraMap ℝ ℂ) = (ω : ℂ) • 1 := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  have hspec : ∀ lam : ℂ, lam ∈ spectrum ℂ ((realify P (ω • 1)).map (algebraMap ℝ ℂ)) ↔
      lam - I * ω ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ∨
        lam + I * ω ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
    intro lam
    rw [mem_spectrum_realify_iff, e, smul_smul, sub_eq_add_neg, ← neg_smul,
      mem_spectrum_add_smul_one_iff, mem_spectrum_add_smul_one_iff, sub_neg_eq_add]
  rw [spectrallyStable_iff_forall_spectrum, spectrallyStable_iff_forall_spectrum]
  constructor
  · intro h μ hμ
    have h1 := h (μ + I * ω) ((hspec _).mpr (Or.inl (by rwa [add_sub_cancel_right])))
    simpa using h1
  · intro h lam hlam
    rcases (hspec lam).mp hlam with h1 | h1
    · simpa using h _ h1
    · simpa using h _ h1

/-- **Averaged matrix of the rotated system.** `∫ₐᵇ (A ⊗ I + ω I ⊗ J) = (∫ₐᵇ A) ⊗ I + (b − a) ω I ⊗ J`;
in particular `∫₀ᵀ A = T Ā` gives the averaged matrix `Ā ⊗ I + ω I ⊗ J`. -/
@[tmio T, powerlib_foundation] theorem integral_realify {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) (ω a b : ℝ) :
    ∫ r in a..b, realify (A r) (ω • 1) = realify (∫ r in a..b, A r) (((b - a) * ω) • 1) := by
  set L₁ := LinearMap.toContinuousLinearMap (kronOne (X := X)) with hL₁
  have hreal : ∀ P Q : Matrix X X ℝ, realify P Q = L₁ P + kronQuarter Q := fun _ _ => rfl
  simp only [hreal]
  have hc : Continuous fun r => L₁ (A r) := L₁.continuous.comp hA
  rw [intervalIntegral.integral_add (hc.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const]
  congr 1
  · exact L₁.intervalIntegral_comp_comm (hA.intervalIntegrable a b)
  · rw [← map_smul, smul_smul]

/-- The mean trace of the rotated system is twice that of `ẋ = A(t) x`. -/
@[tmio T, powerlib_foundation] theorem integral_trace_realify (A : ℝ → Matrix X X ℝ)
    (ω a b : ℝ) :
    ∫ r in a..b, (realify (A r) (ω • 1)).trace = 2 * ∫ r in a..b, (A r).trace := by
  simp only [trace_realify, intervalIntegral.integral_const_mul]

end Data

/-! ## Frequency locking fails -/

/-- **A parametric instability that is not frequency locked.** Let `ẋ = A(t) x` be a continuous
`T`-periodic two-state system with negative mean trace that is Floquet unstable — by
`Periodic.im_eq_zero_of_integral_trace_neg` its unstable multiplier is real, the mode is locked to
the pump (`Periodic.real_multiplier_of_floquetUnstable`). Rotate a second copy against it at the
rate `ω` with `sin(ωT) ≠ 0`: the four-state system `ẋ = (A(t) ⊗ I + ω I ⊗ J) x` still has negative
mean trace and is Floquet unstable, but every multiplier on or outside the unit circle is
non-real (`e^{±iωT} r`, `r` real): no real multiplier carries the instability, and the Floquet
frequencies of the unstable modes lie in `±ω + (Ω/2)ℤ`, `Ω = 2π/T`, off the locked lattice
`(Ω/2)ℤ` (`ParametricResonance.Signature.floquet_factor`). -/
@[tmio T, powerlib_foundation] theorem unlocked {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {T : ℝ}
    (hA : Continuous A) (hP : Periodic A T) (hT : 0 < T)
    (htr : ∫ r in (0 : ℝ)..T, (A r).trace < 0) (hun : FloquetUnstable A T) {ω : ℝ}
    (hsin : Real.sin (ω * T) ≠ 0) :
    ∫ r in (0 : ℝ)..T, (realify (A r) (ω • 1)).trace < 0 ∧
      FloquetUnstable (fun r => realify (A r) (ω • 1)) T ∧
      ∀ lam ∈ spectrum ℂ ((monodromy (fun r => realify (A r) (ω • 1)) T 0).map
        (algebraMap ℝ ℂ)), 1 ≤ ‖lam‖ → lam.im ≠ 0 := by
  refine ⟨by rw [integral_trace_realify]; linarith, ?_, ?_⟩
  · obtain ⟨μ, hμ, hμ1⟩ := hun
    refine ⟨Complex.exp ((ω * T : ℝ) * I) * μ,
      (mem_spectrum_monodromy_realify_iff hA hP hT ω _).mpr ⟨μ, hμ, Or.inl rfl⟩, ?_⟩
    rwa [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · intro lam hlam h1
    obtain ⟨μ, hμ, h | h⟩ := (mem_spectrum_monodromy_realify_iff hA hP hT ω lam).mp hlam <;>
    · have hnorm : ‖lam‖ = ‖μ‖ := by
        rw [h, norm_mul]
        first
          | rw [Complex.norm_exp_ofReal_mul_I, one_mul]
          | rw [show -(((ω * T : ℝ) : ℂ) * I) = ((-(ω * T) : ℝ) : ℂ) * I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I, one_mul]
      have hμim : μ.im = 0 := im_eq_zero_of_integral_trace_neg hA hP htr hμ (hnorm ▸ h1)
      have hμre : μ.re ≠ 0 := by
        intro h0
        have : μ = 0 := Complex.ext h0 hμim
        rw [hnorm, this, norm_zero] at h1
        linarith
      rw [h, Complex.mul_im, hμim, mul_zero, zero_add]
      first
        | rw [Complex.exp_ofReal_mul_I_im]
          exact mul_ne_zero hsin hμre
        | rw [show -(((ω * T : ℝ) : ℂ) * I) = ((-(ω * T) : ℝ) : ℂ) * I by push_cast; ring,
            Complex.exp_ofReal_mul_I_im, Real.sin_neg]
          exact mul_ne_zero (neg_ne_zero.mpr hsin) hμre

/-! ## An exact instance: the 2:1 normal form rotated against itself -/

section Instance

variable {σ Ω ω : ℝ} {c : ℂ}

@[tmio T, powerlib_foundation] private theorem pump_sq (c : ℂ) (ω t : ℝ) :
    pumpRe c ω t ^ 2 + pumpIm c ω t ^ 2 = ‖c‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pumpRe, pumpIm]
  linear_combination (c.re ^ 2 + c.im ^ 2) * Real.sin_sq_add_cos_sq (ω * t)

/-- The frozen matrices of the normal form `ż = (−σ + iΩ) z + c e^{iωt} z̄` are Hurwitz for
`σ > 0` and `|c|² < σ² + Ω²` (trace `−2σ`, determinant `σ² + Ω² − |c|²`). -/
@[tmio T, powerlib_foundation] theorem nf_frozen_isHurwitz (hσ : 0 < σ)
    (hc : ‖c‖ ^ 2 < σ ^ 2 + Ω ^ 2) (t : ℝ) : LinearSystems.IsHurwitz (nfMatrix σ Ω ω c t) := by
  rw [Criteria.isHurwitz_fin_two_iff, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [nfMatrix, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one, cons_val_one]
  have := pump_sq c ω t
  constructor <;> nlinarith

/-- The pump averages out over a period: `∫₀^{2π/ω} nfMatrix = (2π/ω) [[−σ, −Ω], [Ω, −σ]]`. -/
@[tmio T, powerlib_foundation] theorem integral_nfMatrix (hω : 0 < ω) (c : ℂ) :
    ∫ t in (0 : ℝ)..2 * Real.pi / ω, nfMatrix σ Ω ω c t =
      (2 * Real.pi / ω) • !![-σ, -Ω; Ω, -σ] := by
  set E₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  set E₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  have hsplit : (fun t => nfMatrix σ Ω ω c t) =
      fun t => !![-σ, -Ω; Ω, -σ] + pumpRe c ω t • E₁ + pumpIm c ω t • E₂ := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nfMatrix, E₁, E₂]
    all_goals ring
  have hcos : ∫ t in (0 : ℝ)..2 * Real.pi / ω, Real.cos (ω * t) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hω.ne', integral_cos,
      show ω * (2 * Real.pi / ω) = 2 * Real.pi by field_simp]
    simp
  have hsin : ∫ t in (0 : ℝ)..2 * Real.pi / ω, Real.sin (ω * t) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hω.ne', integral_sin,
      show ω * (2 * Real.pi / ω) = 2 * Real.pi by field_simp]
    simp
  have hcc : Continuous fun t => Real.cos (ω * t) := by fun_prop
  have hsc : Continuous fun t => Real.sin (ω * t) := by fun_prop
  have hRe : ∫ t in (0 : ℝ)..2 * Real.pi / ω, pumpRe c ω t = 0 := by
    simp only [pumpRe]
    rw [intervalIntegral.integral_sub ((hcc.const_mul _).intervalIntegrable _ _)
      ((hsc.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hcos, hsin]
    ring
  have hIm : ∫ t in (0 : ℝ)..2 * Real.pi / ω, pumpIm c ω t = 0 := by
    simp only [pumpIm]
    rw [intervalIntegral.integral_add ((hsc.const_mul _).intervalIntegrable _ _)
      ((hcc.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hcos, hsin]
    ring
  have hpr : Continuous fun t => pumpRe c ω t := by simp only [pumpRe]; fun_prop
  have hpi : Continuous fun t => pumpIm c ω t := by simp only [pumpIm]; fun_prop
  have hf : Continuous fun t => !![-σ, -Ω; Ω, -σ] + pumpRe c ω t • E₁ :=
    continuous_const.add (hpr.smul continuous_const)
  have hg : Continuous fun t => pumpIm c ω t • E₂ := hpi.smul continuous_const
  have hg1 : Continuous fun t => pumpRe c ω t • E₁ := hpr.smul continuous_const
  rw [hsplit, intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const (hg1.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, hRe, hIm]
  simp

/-- **Combination resonance, exact four-state instance.** Take the 2:1 normal form at exact
resonance, `ż = (−σ + iΩ) z + c e^{2iΩt} z̄` (pump frequency `2Ω`, period `T = 2π/(2Ω)`), with
`σ > 0` and `σ² < |c|² < σ² + Ω²`, and rotate a second copy against it at the rate `ω` with
`sin(ωT) ≠ 0`: the four-state system `ẋ = (A(t) ⊗ I + ω I ⊗ J) x` (states relabelled by
`Fin 2 × Fin 2 ≃ Fin 4` where Hurwitz stability is stated) has
* Hurwitz frozen matrices at every instant and a Hurwitz averaged matrix
  `[[−σ, −Ω], [Ω, −σ]] ⊗ I + ω I ⊗ J` (small-signal analysis of the frozen or averaged system
  predicts stability);
* negative mean trace;
* a Floquet multiplier outside the unit circle, and every multiplier on or outside the unit circle
  non-real (`e^{±iωT} r` with `r` a real multiplier of the normal form, `unlocked`): a
  parametric instability that is not locked to the pump. -/
@[tmio T, powerlib_foundation] theorem combination_resonance (hσ : 0 < σ) (hΩ : 0 < Ω)
    (hc₁ : σ ^ 2 < ‖c‖ ^ 2) (hc₂ : ‖c‖ ^ 2 < σ ^ 2 + Ω ^ 2)
    (hsin : Real.sin (ω * (2 * Real.pi / (2 * Ω))) ≠ 0) :
    (∀ t, LinearSystems.IsHurwitz ((realify (nfMatrix σ Ω (2 * Ω) c t) (ω • 1)).reindex
      finProdFinEquiv finProdFinEquiv)) ∧
    (∫ t in (0 : ℝ)..2 * Real.pi / (2 * Ω), realify (nfMatrix σ Ω (2 * Ω) c t) (ω • 1)) =
      (2 * Real.pi / (2 * Ω)) • realify !![-σ, -Ω; Ω, -σ] (ω • 1) ∧
    LinearSystems.IsHurwitz ((realify !![-σ, -Ω; Ω, -σ] (ω • 1)).reindex
      finProdFinEquiv finProdFinEquiv) ∧
    ∫ t in (0 : ℝ)..2 * Real.pi / (2 * Ω), (realify (nfMatrix σ Ω (2 * Ω) c t) (ω • 1)).trace < 0 ∧
    FloquetUnstable (fun t => realify (nfMatrix σ Ω (2 * Ω) c t) (ω • 1))
      (2 * Real.pi / (2 * Ω)) ∧
    ∀ lam ∈ spectrum ℂ ((monodromy (fun t => realify (nfMatrix σ Ω (2 * Ω) c t) (ω • 1))
      (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ)), 1 ≤ ‖lam‖ → lam.im ≠ 0 := by
  have h2Ω : 0 < 2 * Ω := by positivity
  set T := 2 * Real.pi / (2 * Ω) with hT
  have hT0 : 0 < T := by positivity
  have hA := ParametricResonance.NormalForm.continuous_nfMatrix σ Ω (2 * Ω) c
  have hP := ParametricResonance.NormalForm.periodic_nfMatrix σ Ω h2Ω.ne' c
  have htrA : ∀ t, (nfMatrix σ Ω (2 * Ω) c t).trace = -(2 * σ) := fun t => by
    rw [Matrix.trace_fin_two]; simp [nfMatrix]; ring
  have htr : ∫ r in (0 : ℝ)..T, (nfMatrix σ Ω (2 * Ω) c r).trace < 0 := by
    simp only [htrA, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    nlinarith
  have hun := ParametricResonance.NormalForm.floquetUnstable_nf_of_lt σ Ω h2Ω c
    (by rw [show 2 * Ω / 2 - Ω = 0 by ring]; linarith)
  have hhur : ∀ N : Matrix (Fin 2) (Fin 2) ℝ, LinearSystems.IsHurwitz N →
      LinearSystems.IsHurwitz ((realify N (ω • 1)).reindex finProdFinEquiv finProdFinEquiv) :=
    fun N hN => by
      rw [← Linear.spectrallyStable_iff_isHurwitz, Linear.spectrallyStable_reindex,
        spectrallyStable_realify_iff, Linear.spectrallyStable_iff_isHurwitz]
      exact hN
  obtain ⟨h1, h2, h3⟩ := unlocked hA hP hT0 htr hun hsin
  refine ⟨fun t => hhur _ (nf_frozen_isHurwitz hσ (by linarith) t), ?_, hhur _ ?_, h1, h2, h3⟩
  · rw [integral_realify hA, integral_nfMatrix h2Ω, sub_zero,
      show ((2 * Real.pi / (2 * Ω)) * ω) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        (2 * Real.pi / (2 * Ω)) • (ω • 1) by rw [smul_smul], realify_smul]
  · rw [Criteria.isHurwitz_fin_two_of_iff]
    constructor <;> nlinarith

end Instance

/-! ## Every dimension `n ≥ 4`: a decoupled stable block -/

section Padding

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- `P ↦ diag(P, 0)`. -/
def blockLeft : Matrix X X ℝ →ₗ[ℝ] Matrix (X ⊕ Y) (X ⊕ Y) ℝ where
  toFun P := fromBlocks P 0 0 0
  map_add' P P' := by rw [fromBlocks_add]; simp
  map_smul' c P := by rw [RingHom.id_apply, fromBlocks_smul]; simp

/-- `R ↦ diag(0, R)`. -/
def blockRight : Matrix Y Y ℝ →ₗ[ℝ] Matrix (X ⊕ Y) (X ⊕ Y) ℝ where
  toFun R := fromBlocks 0 0 0 R
  map_add' R R' := by rw [fromBlocks_add]; simp
  map_smul' c R := by rw [RingHom.id_apply, fromBlocks_smul]; simp

/-- **Transition matrix of a decoupled block system.** For a continuous `T`-periodic `A` and a
constant `C`, `ẋ = diag(A(t), C) x` has `Φ(t, s) = diag(Φ_A(t, s), e^{(t − s)C})`. -/
@[tmio T, powerlib_foundation] theorem transition_fromBlocks {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) {T : ℝ} (hP : Periodic A T) (hT : 0 < T) (C : Matrix Y Y ℝ) {s t : ℝ}
    (hst : s ≤ t) :
    transition (fun r => fromBlocks (A r) 0 0 C) t s =
      fromBlocks (transition A t s) 0 0 (NormedSpace.exp ((t - s) • C)) := by
  set L₁ := LinearMap.toContinuousLinearMap (blockLeft (X := X) (Y := Y)) with hL₁
  set L₂ := LinearMap.toContinuousLinearMap (blockRight (X := X) (Y := Y)) with hL₂
  have hblk : ∀ (P : Matrix X X ℝ) (R : Matrix Y Y ℝ), fromBlocks P 0 0 R = L₁ P + L₂ R :=
    fun P R => by
      show fromBlocks P 0 0 R = fromBlocks P 0 0 0 + fromBlocks 0 0 0 R
      rw [fromBlocks_add]; simp
  have hAc : Continuous fun r => fromBlocks (A r) 0 0 C := by
    simp only [hblk]; exact (L₁.continuous.comp hA).add continuous_const
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hAc (fun r => by simp only [hP r]) hT
  set Yf : ℝ → Matrix (X ⊕ Y) (X ⊕ Y) ℝ := fun r =>
    fromBlocks (transition A r s) 0 0 (NormedSpace.exp ((r - s) • C)) with hYf
  have hderiv : ∀ r, HasDerivAt Yf (fromBlocks (A r) 0 0 C * Yf r) r := by
    intro r
    have hΦ := Dynamics.stm_hasDerivAt hA r s
    have hE := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) C (r - s)).scomp r
      ((hasDerivAt_id' r).sub_const s)
    simp only [one_smul] at hE
    have h := (L₁.hasFDerivAt.comp_hasDerivAt r hΦ).add (L₂.hasFDerivAt.comp_hasDerivAt r hE)
    have hfun : Yf = fun r => L₁ (transition A r s) + L₂ (NormedSpace.exp ((r - s) • C)) := by
      funext r; exact hblk _ _
    rw [hfun]
    refine h.congr_deriv ?_
    calc L₁ (A r * transition A r s) + L₂ (C * NormedSpace.exp ((r - s) • C))
        = fromBlocks (A r * transition A r s) 0 0 (C * NormedSpace.exp ((r - s) • C)) :=
          (hblk _ _).symm
      _ = fromBlocks (A r) 0 0 C *
            fromBlocks (transition A r s) 0 0 (NormedSpace.exp ((r - s) • C)) := by
          rw [fromBlocks_multiply]; simp
      _ = _ := congrArg _ (hblk _ _)
  have hcurve : IsIntegralCurveOn Yf (matField fun r => fromBlocks (A r) 0 0 C) (Ici s) :=
    fun r _ => (hderiv r).hasDerivWithinAt
  have h := transition_unique hAc hM hcurve t hst
  have hYs : Yf s = 1 := by
    simp [hYf, LinearSystems.stateTransitionMatrix_self, fromBlocks_one]
  rw [hYs, Matrix.mul_one] at h
  exact h.symm

/-- The eigenvalues of `diag(P, R)` are those of `P` and those of `R`. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_fromBlocks_iff (P : Matrix X X ℝ)
    (R : Matrix Y Y ℝ) (lam : ℂ) :
    lam ∈ spectrum ℂ ((fromBlocks P 0 0 R).map (algebraMap ℝ ℂ)) ↔
      lam ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ∨ lam ∈ spectrum ℂ (R.map (algebraMap ℝ ℂ)) := by
  simp only [LTI.mem_spectrum_iff_exists_eigvec, fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  constructor
  · rintro ⟨w, hw, h⟩
    rw [fromBlocks_mulVec] at h
    simp only [Matrix.zero_mulVec, add_zero, zero_add] at h
    have h1 : P.map (algebraMap ℝ ℂ) *ᵥ (w ∘ Sum.inl) = lam • (w ∘ Sum.inl) := by
      funext i; have := congrFun h (Sum.inl i); simpa using this
    have h2 : R.map (algebraMap ℝ ℂ) *ᵥ (w ∘ Sum.inr) = lam • (w ∘ Sum.inr) := by
      funext i; have := congrFun h (Sum.inr i); simpa using this
    by_cases hl : w ∘ Sum.inl = 0
    · refine Or.inr ⟨w ∘ Sum.inr, fun hr => hw ?_, h2⟩
      funext i
      rcases i with i | i
      · exact congrFun hl i
      · exact congrFun hr i
    · exact Or.inl ⟨w ∘ Sum.inl, hl, h1⟩
  · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
    · refine ⟨Sum.elim v 0, fun h0 => hv (funext fun i => congrFun h0 (Sum.inl i)), ?_⟩
      rw [fromBlocks_mulVec]
      funext i
      rcases i with i | i
      · simpa [Function.comp_def] using congrFun h i
      · simp [Function.comp_def, Matrix.mulVec, dotProduct]
    · refine ⟨Sum.elim 0 v, fun h0 => hv (funext fun i => congrFun h0 (Sum.inr i)), ?_⟩
      rw [fromBlocks_mulVec]
      funext i
      rcases i with i | i
      · simp [Function.comp_def, Matrix.mulVec, dotProduct]
      · simpa [Function.comp_def] using congrFun h i

omit [DecidableEq X] [DecidableEq Y] in
/-- `tr diag(P, R) = tr P + tr R`. -/
@[tmio T, powerlib_foundation] theorem trace_fromBlocks_zero (P : Matrix X X ℝ)
    (R : Matrix Y Y ℝ) : (fromBlocks P 0 0 R).trace = P.trace + R.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- **Frequency locking fails in every dimension `n ≥ 4`.** In the setting of `unlocked`, append a
decoupled constant Hurwitz block `C` on `k` states (`k ≥ 0`): the `(4 + k)`-state system
`ẋ = diag(A(t) ⊗ I + ω I ⊗ J, C) x` has negative mean trace, is Floquet unstable, every multiplier
on or outside the unit circle is non-real, and its frozen matrices are Hurwitz whenever those of
`A` are. -/
@[tmio T, powerlib_foundation] theorem unlocked_of_card {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {T : ℝ}
    (hA : Continuous A) (hP : Periodic A T) (hT : 0 < T)
    (htr : ∫ r in (0 : ℝ)..T, (A r).trace < 0) (hun : FloquetUnstable A T) {ω : ℝ}
    (hsin : Real.sin (ω * T) ≠ 0) {k : ℕ} {C : Matrix (Fin k) (Fin k) ℝ}
    (hC : LinearSystems.IsHurwitz C) :
    ∫ r in (0 : ℝ)..T, (fromBlocks (realify (A r) (ω • 1)) 0 0 C).trace < 0 ∧
      FloquetUnstable (fun r => fromBlocks (realify (A r) (ω • 1)) 0 0 C) T ∧
      (∀ lam ∈ spectrum ℂ ((monodromy (fun r => fromBlocks (realify (A r) (ω • 1)) 0 0 C) T 0).map
        (algebraMap ℝ ℂ)), 1 ≤ ‖lam‖ → lam.im ≠ 0) ∧
      ((∀ t, LinearSystems.IsHurwitz (A t)) →
        ∀ t, Linear.SpectrallyStable (fromBlocks (realify (A t) (ω • 1)) 0 0 C)) := by
  obtain ⟨h1, h2, h3⟩ := unlocked hA hP hT htr hun hsin
  set A₄ := fun r => realify (A r) (ω • 1) with hA₄
  have hA₄c : Continuous A₄ := by
    have : A₄ = fun r => LinearMap.toContinuousLinearMap (kronOne (X := Fin 2)) (A r) +
        kronQuarter (ω • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := rfl
    rw [this]; exact ((LinearMap.toContinuousLinearMap kronOne).continuous.comp hA).add
      continuous_const
  have hA₄p : Periodic A₄ T := fun r => by simp only [hA₄, hP r]
  have hmono : monodromy (fun r => fromBlocks (A₄ r) 0 0 C) T 0 =
      fromBlocks (monodromy A₄ T 0) 0 0 (NormedSpace.exp (T • C)) := by
    simp only [monodromy]
    rw [transition_fromBlocks hA₄c hA₄p hT C (by linarith), zero_add, sub_zero]
  have hS := (LTI.isHurwitz_iff_schurStable_exp C hT).mp hC
  have hsmall : ∀ lam ∈ spectrum ℂ ((NormedSpace.exp (T • C)).map (algebraMap ℝ ℂ)),
      ‖lam‖ < 1 := fun lam hlam => by
    obtain ⟨v, hv, h⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hlam
    exact hS lam v hv h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [trace_fromBlocks_zero]
    rw [intervalIntegral.integral_add (by
        exact hA₄c.matrix_trace.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hCtr : C.trace ≤ 0 := by
      obtain ⟨K, α, hα, hexp⟩ := (Robust.isHurwitz_iff_exists_exp_bound C).mp hC
      have := Robust.card_mul_le_neg_trace hexp
      rw [Fintype.card_fin] at this
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  · obtain ⟨μ, hμ, hμ1⟩ := h2
    exact ⟨μ, by rw [hmono, mem_spectrum_fromBlocks_iff]; exact Or.inl hμ, hμ1⟩
  · intro lam hlam h1'
    rw [hmono, mem_spectrum_fromBlocks_iff] at hlam
    rcases hlam with hlam | hlam
    · exact h3 lam hlam h1'
    · exact absurd h1' (not_le.mpr (hsmall lam hlam))
  · intro hH t
    rw [spectrallyStable_iff_forall_spectrum]
    intro lam hlam
    rw [mem_spectrum_fromBlocks_iff] at hlam
    rcases hlam with hlam | hlam
    · exact (spectrallyStable_iff_forall_spectrum _).mp
        ((spectrallyStable_realify_iff _ ω).mpr
          ((Linear.spectrallyStable_iff_isHurwitz _).mpr (hH t))) lam hlam
    · exact (spectrallyStable_iff_forall_spectrum _).mp
        ((Linear.spectrallyStable_iff_isHurwitz _).mpr hC) lam hlam

end Padding

end powerlib.Periodic.Combination
