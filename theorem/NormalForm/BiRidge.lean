import theorem.NormalForm.LyapunovCoefficient

/-! # The second and third derivatives of a product of two ridge nonlinearities

The forms `B = D²f(x₀)` and `C = D³f(x₀)` of the field `x ↦ φ(ℓ x) ψ(m x) v` (two scalar
nonlinearities of two linear functionals, times a fixed vector), complexified as
`NormalForm.LyapunovCoefficient.bilinC` and `trilinC`, for the first Lyapunov coefficient of fields
with a product nonlinearity such as `sin(δ − α)/V`. It extends `prodRidge` (`ψ` linear) of
`theorem/NormalForm/LyapunovCoefficient.lean`.

Scope.
* Generic foundation, independent of any model: arbitrary `φ, ψ : ℝ → ℝ` that are `C³` with
  explicit derivative chains (`HasDerivAt φ (φ₁ t) t`, …, everywhere), continuous linear
  functionals `ℓ, m` on `ℝⁿ` and a vector `v`. No engineering import, no family.
* The forms at a point depend only on the germ of the field there
  (`bilinC_congr`, `trilinC_congr`): a field equal to `φ(ℓ x) ψ(m x) v` near `x₀` (for instance with
  `ψ(t) = 1/t` near `t = m x₀ ≠ 0`) has the forms computed here from any `C³` extension.

Source: the Leibniz rule for the second and third derivatives of a product (the Faà di Bruno
formula for a composition with a linear map); the complexified forms of Kuznetsov, *Elements of
Applied Bifurcation Theory* (3rd ed.), §3.5.

Results.
* `biRidge`, `contDiff_biRidge`; `hess_biRidge`, `third_biRidge` (coordinates);
  `bilinC_biRidge`: `B(u, w) = (φ''ψ ℓu ℓw + φ'ψ' (ℓu mw + mu ℓw) + φψ'' mu mw) v`;
  `trilinC_biRidge`: `C(u, w, z) = (φ'''ψ ℓuℓwℓz + φ''ψ' (ℓuℓw mz + ℓu mw ℓz + mu ℓw ℓz)
  + φ'ψ'' (ℓu mw mz + mu ℓw mz + mu mw ℓz) + φψ''' mu mw mz) v`, all derivatives at `ℓ x₀`, `m x₀`.
* `recipSmooth`: a `C^∞` function equal to `(1 + t)⁻¹` for `t > −1/4` (`recipSmooth_eq`,
  `contDiff_recipSmooth`), with its value and derivatives `1, −1, 2, −6` at `0`
  (`recipSmooth_derivs`, `hasDerivAt_recipSmooth_chain`): the reciprocal `1/V` near `V = 1` as an
  input of the laws above.
* `hess_congr`, `third_congr`, `bilinC_congr`, `trilinC_congr`, `jacobianC_congr`,
  `firstLyapunov_congr`, `isCriticalPair_congr`: the forms, the complexified Jacobian, Kuznetsov's
  coefficient and critical pairs at a point depend only on the field near it.
-/

noncomputable section
namespace powerlib.NormalForm.LyapunovCoefficient
open Complex Matrix Set Filter
open scoped ContDiff
open powerlib.Dynamics (State)

variable {n : ℕ}

/-! ## Locality of the forms -/

section Congr

variable {f g : State n → State n} {x₀ : State n}

@[tmio T, powerlib_foundation] theorem jacobianC_congr (h : f =ᶠ[nhds x₀] g) :
    jacobianC f x₀ = jacobianC g x₀ := by
  rw [jacobianC, jacobianC, h.fderiv_eq]

@[tmio T, powerlib_foundation] theorem hess_congr (h : f =ᶠ[nhds x₀] g) (k i j : Fin n) :
    hess f x₀ k i j = hess g x₀ k i j := by
  rw [hess, hess, (h.iteratedFDeriv ℝ 2).eq_of_nhds]

@[tmio T, powerlib_foundation] theorem third_congr (h : f =ᶠ[nhds x₀] g) (k i j l : Fin n) :
    third f x₀ k i j l = third g x₀ k i j l := by
  rw [third, third, (h.iteratedFDeriv ℝ 3).eq_of_nhds]

@[tmio T, powerlib_foundation] theorem bilinC_congr (h : f =ᶠ[nhds x₀] g) :
    bilinC f x₀ = bilinC g x₀ := by
  simp only [bilinC, hess_congr h]

@[tmio T, powerlib_foundation] theorem trilinC_congr (h : f =ᶠ[nhds x₀] g) :
    trilinC f x₀ = trilinC g x₀ := by
  simp only [trilinC, third_congr h]

@[tmio T, powerlib_foundation] theorem firstLyapunov_congr (h : f =ᶠ[nhds x₀] g) (ω₀ : ℝ)
    (q p : Fin n → ℂ) : firstLyapunov f x₀ ω₀ q p = firstLyapunov g x₀ ω₀ q p := by
  simp only [firstLyapunov, bilinC_congr h, trilinC_congr h, jacobianC_congr h]

@[tmio T, powerlib_foundation] theorem isCriticalPair_congr (h : f =ᶠ[nhds x₀] g) {ω₀ : ℝ}
    {q p : Fin n → ℂ} : IsCriticalPair f x₀ ω₀ q p ↔ IsCriticalPair g x₀ ω₀ q p := by
  constructor <;> rintro ⟨h0, hω, hr, hl, hn⟩
  · exact ⟨by rw [← h.eq_of_nhds]; exact h0, hω, by rw [← jacobianC_congr h]; exact hr,
      by rw [← jacobianC_congr h]; exact hl, hn⟩
  · exact ⟨by rw [h.eq_of_nhds]; exact h0, hω, by rw [jacobianC_congr h]; exact hr,
      by rw [jacobianC_congr h]; exact hl, hn⟩

end Congr

/-! ## Products of two ridge nonlinearities -/

/-- The field `x ↦ φ(ℓ x) ψ(m x) v`. -/
def biRidge (ℓ m : State n →L[ℝ] ℝ) (φ ψ : ℝ → ℝ) (v : State n) (x : State n) : State n :=
  (φ (ℓ x) * ψ (m x)) • v

section BiRidge

variable (ℓ m : State n →L[ℝ] ℝ) (v : State n) {φ φ1 φ2 φ3 ψ ψ1 ψ2 ψ3 : ℝ → ℝ}

@[tmio T, powerlib_foundation] theorem contDiff_biRidge (hφ : ContDiff ℝ 3 φ)
    (hψ : ContDiff ℝ 3 ψ) : ContDiff ℝ 3 (biRidge ℓ m φ ψ v) :=
  ((hφ.comp ℓ.contDiff).mul (hψ.comp m.contDiff)).smul contDiff_const

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_biRidge
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t) (y : State n) :
    HasFDerivAt (biRidge ℓ m φ ψ v)
      ((φ1 (ℓ y) * ψ (m y)) • ℓ.smulRight v + (φ (ℓ y) * ψ1 (m y)) • m.smulRight v) y := by
  have h := (((h1 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).mul
    ((k1 (m y)).comp_hasFDerivAt y m.hasFDerivAt)).smul_const v
  refine h.congr_fderiv ?_
  ext1 w
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply, smul_smul, ← add_smul]
  congr 1
  ring

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_biRidge_col
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t) (k2 : ∀ t, HasDerivAt ψ1 (ψ2 t) t) (w y : State n) :
    HasFDerivAt (fun y => ((φ1 (ℓ y) * ψ (m y)) • ℓ.smulRight v +
        (φ (ℓ y) * ψ1 (m y)) • m.smulRight v) w)
      (((φ2 (ℓ y) * ψ (m y) * ℓ w + φ1 (ℓ y) * ψ1 (m y) * m w) • ℓ +
        (φ1 (ℓ y) * ψ1 (m y) * ℓ w + φ (ℓ y) * ψ2 (m y) * m w) • m).smulRight v) y := by
  have hφ1 := (h1 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt
  have hφ2 := (h2 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt
  have hψ1 := (k1 (m y)).comp_hasFDerivAt y m.hasFDerivAt
  have hψ2 := (k2 (m y)).comp_hasFDerivAt y m.hasFDerivAt
  have h := (((hφ2.mul hψ1).mul_const (ℓ w)).add ((hφ1.mul hψ2).mul_const (m w))).smul_const v
  have e : (fun y => ((φ1 (ℓ y) * ψ (m y)) • ℓ.smulRight v +
        (φ (ℓ y) * ψ1 (m y)) • m.smulRight v) w) =
      fun y => (φ1 (ℓ y) * ψ (m y) * ℓ w + φ (ℓ y) * ψ1 (m y) * m w) • v := by
    funext z
    simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
      smul_smul, ← add_smul]
  rw [e]
  refine h.congr_fderiv ?_
  ext1 u
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply, smul_smul]
  congr 1
  ring

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_biRidge_col2
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t) (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t)
    (k2 : ∀ t, HasDerivAt ψ1 (ψ2 t) t) (k3 : ∀ t, HasDerivAt ψ2 (ψ3 t) t) (w u y : State n) :
    HasFDerivAt
      (fun y => (((φ2 (ℓ y) * ψ (m y) * ℓ w + φ1 (ℓ y) * ψ1 (m y) * m w) • ℓ +
        (φ1 (ℓ y) * ψ1 (m y) * ℓ w + φ (ℓ y) * ψ2 (m y) * m w) • m).smulRight v) u)
      (((φ3 (ℓ y) * ψ (m y) * ℓ w * ℓ u + φ2 (ℓ y) * ψ1 (m y) * (m w * ℓ u + ℓ w * m u) +
          φ1 (ℓ y) * ψ2 (m y) * m w * m u) • ℓ +
        (φ2 (ℓ y) * ψ1 (m y) * ℓ w * ℓ u + φ1 (ℓ y) * ψ2 (m y) * (m w * ℓ u + ℓ w * m u) +
          φ (ℓ y) * ψ3 (m y) * m w * m u) • m).smulRight v) y := by
  have a0 := (h1 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt
  have a1 := (h2 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt
  have a2 := (h3 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt
  have b0 := (k1 (m y)).comp_hasFDerivAt y m.hasFDerivAt
  have b1 := (k2 (m y)).comp_hasFDerivAt y m.hasFDerivAt
  have b2 := (k3 (m y)).comp_hasFDerivAt y m.hasFDerivAt
  have h := ((((a2.mul b0).mul_const (ℓ w * ℓ u)).add
    ((a1.mul b1).mul_const (m w * ℓ u + ℓ w * m u))).add
    ((a0.mul b2).mul_const (m w * m u))).smul_const v
  have e : (fun y => (((φ2 (ℓ y) * ψ (m y) * ℓ w + φ1 (ℓ y) * ψ1 (m y) * m w) • ℓ +
        (φ1 (ℓ y) * ψ1 (m y) * ℓ w + φ (ℓ y) * ψ2 (m y) * m w) • m).smulRight v) u) =
      fun y => (φ2 (ℓ y) * ψ (m y) * (ℓ w * ℓ u) + φ1 (ℓ y) * ψ1 (m y) *
        (m w * ℓ u + ℓ w * m u) + φ (ℓ y) * ψ2 (m y) * (m w * m u)) • v := by
    funext z
    simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul]
    congr 1
    ring
  rw [e]
  refine h.congr_fderiv ?_
  ext1 z'
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply, smul_smul]
  congr 1
  ring

/-- `B` of `φ(ℓ x) ψ(m x) v` in coordinates. -/
@[tmio T, powerlib_foundation] theorem hess_biRidge (hφ : ContDiff ℝ 3 φ) (hψ : ContDiff ℝ 3 ψ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t) (k2 : ∀ t, HasDerivAt ψ1 (ψ2 t) t) (x₀ : State n)
    (k i j : Fin n) :
    hess (biRidge ℓ m φ ψ v) x₀ k i j =
      ((φ2 (ℓ x₀) * ψ (m x₀) * ℓ (basisVec j) + φ1 (ℓ x₀) * ψ1 (m x₀) * m (basisVec j)) *
          ℓ (basisVec i) +
        (φ1 (ℓ x₀) * ψ1 (m x₀) * ℓ (basisVec j) + φ (ℓ x₀) * ψ2 (m x₀) * m (basisVec j)) *
          m (basisVec i)) * v k := by
  rw [hess_eq_of_hasFDerivAt ((contDiff_biRidge ℓ m v hφ hψ).of_le (by norm_num))
    (hasFDerivAt_biRidge ℓ m v h1 k1) (hasFDerivAt_biRidge_col ℓ m v h1 h2 k1 k2 _ x₀)]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, PiLp.smul_apply]

/-- `C` of `φ(ℓ x) ψ(m x) v` in coordinates. -/
@[tmio T, powerlib_foundation] theorem third_biRidge (hφ : ContDiff ℝ 3 φ) (hψ : ContDiff ℝ 3 ψ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t) (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t)
    (k2 : ∀ t, HasDerivAt ψ1 (ψ2 t) t) (k3 : ∀ t, HasDerivAt ψ2 (ψ3 t) t) (x₀ : State n)
    (k i j l : Fin n) :
    third (biRidge ℓ m φ ψ v) x₀ k i j l =
      ((φ3 (ℓ x₀) * ψ (m x₀) * ℓ (basisVec l) * ℓ (basisVec j) +
          φ2 (ℓ x₀) * ψ1 (m x₀) * (m (basisVec l) * ℓ (basisVec j) +
            ℓ (basisVec l) * m (basisVec j)) +
          φ1 (ℓ x₀) * ψ2 (m x₀) * m (basisVec l) * m (basisVec j)) * ℓ (basisVec i) +
        (φ2 (ℓ x₀) * ψ1 (m x₀) * ℓ (basisVec l) * ℓ (basisVec j) +
          φ1 (ℓ x₀) * ψ2 (m x₀) * (m (basisVec l) * ℓ (basisVec j) +
            ℓ (basisVec l) * m (basisVec j)) +
          φ (ℓ x₀) * ψ3 (m x₀) * m (basisVec l) * m (basisVec j)) * m (basisVec i)) * v k := by
  rw [third_eq_of_hasFDerivAt (contDiff_biRidge ℓ m v hφ hψ) (hasFDerivAt_biRidge ℓ m v h1 k1)
    (hasFDerivAt_biRidge_col ℓ m v h1 h2 k1 k2 _)
    (hasFDerivAt_biRidge_col2 ℓ m v h1 h2 h3 k1 k2 k3 _ _ x₀)]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, PiLp.smul_apply]

@[tmio T, powerlib_foundation] private theorem funC_mul2' (a b : State n →L[ℝ] ℝ)
    (u w : Fin n → ℂ) :
    funC a u * funC b w = ∑ i, ∑ j, (a (basisVec i) : ℂ) * (b (basisVec j) : ℂ) * u i * w j := by
  simp only [funC, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[tmio T, powerlib_foundation] private theorem funC_mul3' (a b c : State n →L[ℝ] ℝ)
    (u w z : Fin n → ℂ) :
    funC a u * funC b w * funC c z = ∑ i, ∑ j, ∑ l, (a (basisVec i) : ℂ) *
      (b (basisVec j) : ℂ) * (c (basisVec l) : ℂ) * u i * w j * z l := by
  rw [funC_mul2', Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [funC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `B(u, w) = (φ''ψ ℓ(u) ℓ(w) + φ'ψ' (ℓ(u) m(w) + m(u) ℓ(w)) + φψ'' m(u) m(w)) v` for
`φ(ℓ x) ψ(m x) v`, the derivatives at `ℓ x₀`, `m x₀`. -/
@[tmio T, powerlib_foundation] theorem bilinC_biRidge (hφ : ContDiff ℝ 3 φ) (hψ : ContDiff ℝ 3 ψ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t) (k2 : ∀ t, HasDerivAt ψ1 (ψ2 t) t) (x₀ : State n)
    (u w : Fin n → ℂ) :
    bilinC (biRidge ℓ m φ ψ v) x₀ u w =
      (((φ2 (ℓ x₀) * ψ (m x₀) : ℝ) : ℂ) * (funC ℓ u * funC ℓ w) +
        ((φ1 (ℓ x₀) * ψ1 (m x₀) : ℝ) : ℂ) * (funC ℓ u * funC m w + funC m u * funC ℓ w) +
        ((φ (ℓ x₀) * ψ2 (m x₀) : ℝ) : ℂ) * (funC m u * funC m w)) • toC v := by
  ext k
  rw [bilinC_apply, Pi.smul_apply, smul_eq_mul]
  simp only [funC_mul2']
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, toC_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hess_biRidge ℓ m v hφ hψ h1 h2 k1 k2]
  push_cast
  ring

/-- `C(u, w, z)` for `φ(ℓ x) ψ(m x) v`: the four groups of third derivatives
`φ⁽³⁾ψ`, `φ⁽²⁾ψ⁽¹⁾`, `φ⁽¹⁾ψ⁽²⁾`, `φψ⁽³⁾` at `ℓ x₀`, `m x₀`, each with its symmetrized monomials
in `ℓ` and `m`. -/
@[tmio T, powerlib_foundation] theorem trilinC_biRidge (hφ : ContDiff ℝ 3 φ)
    (hψ : ContDiff ℝ 3 ψ) (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t) (k1 : ∀ t, HasDerivAt ψ (ψ1 t) t)
    (k2 : ∀ t, HasDerivAt ψ1 (ψ2 t) t) (k3 : ∀ t, HasDerivAt ψ2 (ψ3 t) t) (x₀ : State n)
    (u w z : Fin n → ℂ) :
    trilinC (biRidge ℓ m φ ψ v) x₀ u w z =
      (((φ3 (ℓ x₀) * ψ (m x₀) : ℝ) : ℂ) * (funC ℓ u * funC ℓ w * funC ℓ z) +
        ((φ2 (ℓ x₀) * ψ1 (m x₀) : ℝ) : ℂ) * (funC ℓ u * funC ℓ w * funC m z +
          funC ℓ u * funC m w * funC ℓ z + funC m u * funC ℓ w * funC ℓ z) +
        ((φ1 (ℓ x₀) * ψ2 (m x₀) : ℝ) : ℂ) * (funC ℓ u * funC m w * funC m z +
          funC m u * funC ℓ w * funC m z + funC m u * funC m w * funC ℓ z) +
        ((φ (ℓ x₀) * ψ3 (m x₀) : ℝ) : ℂ) * (funC m u * funC m w * funC m z)) • toC v := by
  ext k
  rw [trilinC_apply, Pi.smul_apply, smul_eq_mul]
  simp only [funC_mul3']
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, toC_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [third_biRidge ℓ m v hφ hψ h1 h2 h3 k1 k2 k3]
  push_cast
  ring

end BiRidge

/-! ## A smooth reciprocal -/

/-- A `C^∞` function equal to `(1 + t)⁻¹` for `t > −1/4` (the denominator is glued to `1/2` by
`Real.smoothTransition`): the factor `1/V` near `V = 1` as a globally smooth function. -/
def recipSmooth (t : ℝ) : ℝ :=
  (1 / 2 + (t + 1 / 2) * Real.smoothTransition (4 * (t + 1 / 2)))⁻¹

@[tmio T, powerlib_foundation] private theorem recipSmooth_den_pos (t : ℝ) :
    0 < 1 / 2 + (t + 1 / 2) * Real.smoothTransition (4 * (t + 1 / 2)) := by
  rcases le_or_gt 0 (t + 1 / 2) with h | h
  · have := mul_nonneg h (Real.smoothTransition.nonneg (4 * (t + 1 / 2)))
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]
    norm_num

@[tmio T, powerlib_foundation] theorem contDiff_recipSmooth : ContDiff ℝ ∞ recipSmooth := by
  unfold recipSmooth
  exact (contDiff_const.add ((contDiff_id.add contDiff_const).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul
      (contDiff_id.add contDiff_const))))).inv fun t => (recipSmooth_den_pos t).ne'

@[tmio T, powerlib_foundation] theorem recipSmooth_eq {t : ℝ} (ht : -1 / 4 < t) :
    recipSmooth t = (1 + t)⁻¹ := by
  rw [recipSmooth, Real.smoothTransition.one_of_one_le (by linarith)]
  ring_nf

@[tmio T, powerlib_foundation] private theorem hasDerivAt_mul_zpow_one_add (c : ℝ) (m : ℤ)
    {t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (fun t => c * (1 + t) ^ m) (c * m * (1 + t) ^ (m - 1)) t := by
  have h := ((hasDerivAt_zpow m (1 + t) (Or.inl ht)).comp t
    ((hasDerivAt_id t).const_add 1)).const_mul c
  convert h using 1
  · rfl
  · ring

@[tmio T, powerlib_foundation] private theorem deriv_eventuallyEq_zpow {F : ℝ → ℝ} {c : ℝ} {m : ℤ}
    (h : F =ᶠ[nhds 0] fun t => c * (1 + t) ^ m) :
    deriv F =ᶠ[nhds 0] fun t => c * m * (1 + t) ^ (m - 1) := by
  refine h.deriv.trans ?_
  filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
  exact (hasDerivAt_mul_zpow_one_add c m (by simp at ht; linarith)).deriv

/-- The value and the first three derivatives of `recipSmooth` at `0`: `1, −1, 2, −6`. -/
@[tmio T, powerlib_foundation] theorem recipSmooth_derivs :
    recipSmooth 0 = 1 ∧ deriv recipSmooth 0 = -1 ∧ deriv (deriv recipSmooth) 0 = 2 ∧
      deriv (deriv (deriv recipSmooth)) 0 = -6 := by
  have h0 : recipSmooth =ᶠ[nhds 0] fun t => (1 : ℝ) * (1 + t) ^ (-1 : ℤ) := by
    filter_upwards [Ioi_mem_nhds (show (-1 / 4 : ℝ) < 0 by norm_num)] with t ht
    rw [recipSmooth_eq ht, _root_.zpow_neg_one, one_mul]
  have h1 := deriv_eventuallyEq_zpow h0
  have h2 := deriv_eventuallyEq_zpow h1
  have h3 := deriv_eventuallyEq_zpow h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0.eq_of_nhds]; norm_num
  · rw [h1.eq_of_nhds]; norm_num
  · rw [h2.eq_of_nhds]; norm_num
  · rw [h3.eq_of_nhds]; norm_num

/-- The derivative chain of `recipSmooth`, everywhere. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_recipSmooth_chain :
    (∀ t, HasDerivAt recipSmooth (deriv recipSmooth t) t) ∧
      (∀ t, HasDerivAt (deriv recipSmooth) (deriv (deriv recipSmooth) t) t) ∧
      ∀ t, HasDerivAt (deriv (deriv recipSmooth)) (deriv (deriv (deriv recipSmooth)) t) t := by
  have h := contDiff_recipSmooth
  have d1 : ContDiff ℝ ∞ (deriv recipSmooth) := h.iterate_deriv 1
  have d2 : ContDiff ℝ ∞ (deriv (deriv recipSmooth)) := h.iterate_deriv 2
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · exact (h.differentiable (by simp)).differentiableAt.hasDerivAt
  · exact (d1.differentiable (by simp)).differentiableAt.hasDerivAt
  · exact (d2.differentiable (by simp)).differentiableAt.hasDerivAt

end powerlib.NormalForm.LyapunovCoefficient
