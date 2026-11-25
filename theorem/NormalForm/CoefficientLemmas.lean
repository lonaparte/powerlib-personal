import theorem.NormalForm.LyapunovCoefficient

/-! # Auxiliary laws for the fold and Lyapunov coefficients of explicit fields (foundation)

Small generic laws that the computations of fold and first Lyapunov coefficients of explicit
model fields share: the derivative forms of a translated field, the coordinates of the basis
vectors, the iterated derivatives of the scalar nonlinearities `(c − a t)²`, `c cos t`, `c sin t`,
conjugation of a left eigenvector of a real matrix, and the root of a linear factor.

Scope.
* Fields `f : State n → State n` (`State n = EuclideanSpace ℝ (Fin n)`), points `x₀`, real
  matrices, complex vectors and real scalar functions; nothing here describes a physical system,
  every statement is a generic identity or root-location fact, a foundation result. Model modules
  computing coefficients with `theorem/NormalForm/LyapunovCoefficient.lean` read them (e.g.
  `theorem/GridTiedConverter/GFM/QVDroopFold.lean`, `QVDroopHopf.lean`,
  `QVDroopVirtualFold.lean`, `QVDroopVirtualHopf.lean`).

Source: the definitions `bilinC`, `trilinC`, `hess`, `third`, `basisVec` of
`theorem/NormalForm/LyapunovCoefficient.lean`; Mathlib's `iteratedFDeriv_comp_add_right` and the
derivatives of `sin`, `cos`; elementary algebra.

Results.
* `bilinC_comp_add`, `trilinC_comp_add`: the second- and third-derivative forms of
  `z ↦ f (z + x₀)` at `0` are those of `f` at `x₀`.
* `coord_basisVec`: `coord i (basisVec j) = if i = j then 1 else 0`.
* `iteratedDeriv_affine_sq`, `iteratedDeriv_const_mul_cos`, `iteratedDeriv_const_mul_sin`: the
  second and third derivatives of `(c − a t)²`, `c cos t`, `c sin t`.
* `transpose_mulVec_conj_div`: for a real matrix `A`, if `Aᵀ y = ν y` then
  `Aᵀ (ȳ/z) = ν̄ (ȳ/z)` (the conjugate of a left eigenvector, rescaled, is a left eigenvector for
  the conjugate eigenvalue).
* `re_neg_of_eval_X_add_C`: the root of `s + λ` with `λ > 0` lies in the open left half plane.
-/

noncomputable section
namespace powerlib.NormalForm.LyapunovCoefficient
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord)

variable {n : ℕ}

/-- **Translation of the second-derivative form**: the form of `z ↦ f (z + x₀)` at `0` is the
form of `f` at `x₀`. -/
@[tmio T, powerlib_foundation] theorem bilinC_comp_add (f : State n → State n) (x₀ : State n) :
    bilinC (fun z => f (z + x₀)) 0 = bilinC f x₀ := by
  have hH : hess (fun z => f (z + x₀)) 0 = hess f x₀ := by
    funext k i j; simp only [hess, iteratedFDeriv_comp_add_right, zero_add]
  simp only [bilinC, hH]

/-- **Translation of the third-derivative form**: the form of `z ↦ f (z + x₀)` at `0` is the form
of `f` at `x₀`. -/
@[tmio T, powerlib_foundation] theorem trilinC_comp_add (f : State n → State n) (x₀ : State n) :
    trilinC (fun z => f (z + x₀)) 0 = trilinC f x₀ := by
  have hT : third (fun z => f (z + x₀)) 0 = third f x₀ := by
    funext k i j l; simp only [third, iteratedFDeriv_comp_add_right, zero_add]
  simp only [trilinC, hT]

/-- The coordinates of the basis vectors: `coord i (basisVec j) = if i = j then 1 else 0`. -/
@[tmio T, powerlib_foundation] theorem coord_basisVec (i j : Fin n) :
    coord i (basisVec j) = if i = j then 1 else 0 := by
  simp [Dynamics.coord_apply, basisVec]

/-- The second and third derivatives of `t ↦ (c − a t)²`: `2 a²` and `0`. -/
@[tmio T, powerlib_foundation] theorem iteratedDeriv_affine_sq (c a : ℝ) (t : ℝ) :
    iteratedDeriv 2 (fun t => (c - a * t) ^ 2) t = 2 * a ^ 2 ∧
      iteratedDeriv 3 (fun t => (c - a * t) ^ 2) t = 0 := by
  have h0 : ∀ t, HasDerivAt (fun t => c - a * t) (-a) t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul a).const_sub c
  have h1 : ∀ t, HasDerivAt (fun t => (c - a * t) ^ 2) (-(2 * a * (c - a * t))) t :=
    fun t => ((h0 t).pow 2).congr_deriv (by norm_num; ring)
  have h2 : ∀ t, HasDerivAt (fun t => -(2 * a * (c - a * t))) (2 * a ^ 2) t :=
    fun t => (((h0 t).const_mul (2 * a)).neg).congr_deriv (by ring)
  have h3 : ∀ t, HasDerivAt (fun _ : ℝ => 2 * a ^ 2) 0 t := fun t => hasDerivAt_const t _
  obtain ⟨-, e2, e3⟩ := iteratedDeriv_of_hasDerivAt h1 h2 h3 t
  exact ⟨e2, e3⟩

/-- The second and third derivatives of `t ↦ c cos t`: `−c cos t` and `c sin t`. -/
@[tmio T, powerlib_foundation] theorem iteratedDeriv_const_mul_cos (c : ℝ) (t : ℝ) :
    iteratedDeriv 2 (fun t => c * Real.cos t) t = -(c * Real.cos t) ∧
      iteratedDeriv 3 (fun t => c * Real.cos t) t = c * Real.sin t := by
  have h1 : ∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t := fun t =>
    ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring)
  have h2 : ∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t := fun t =>
    ((Real.hasDerivAt_sin t).const_mul c).neg
  have h3 : ∀ t, HasDerivAt (fun t => -(c * Real.cos t)) (c * Real.sin t) t := fun t =>
    (((Real.hasDerivAt_cos t).const_mul c).neg).congr_deriv (by ring)
  obtain ⟨-, e2, e3⟩ := iteratedDeriv_of_hasDerivAt h1 h2 h3 t
  exact ⟨e2, e3⟩

/-- The second and third derivatives of `t ↦ c sin t`: `−c sin t` and `−c cos t`. -/
@[tmio T, powerlib_foundation] theorem iteratedDeriv_const_mul_sin (c : ℝ) (t : ℝ) :
    iteratedDeriv 2 (fun t => c * Real.sin t) t = -(c * Real.sin t) ∧
      iteratedDeriv 3 (fun t => c * Real.sin t) t = -(c * Real.cos t) := by
  have h1 : ∀ t, HasDerivAt (fun t => c * Real.sin t) (c * Real.cos t) t := fun t =>
    (Real.hasDerivAt_sin t).const_mul c
  have h2 : ∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t := fun t =>
    ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring)
  have h3 : ∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t := fun t =>
    ((Real.hasDerivAt_sin t).const_mul c).neg
  obtain ⟨-, e2, e3⟩ := iteratedDeriv_of_hasDerivAt h1 h2 h3 t
  exact ⟨e2, e3⟩

/-- **Conjugating a left eigenvector of a real matrix**: if `Aᵀ y = ν y` for a real `A`, then
`Aᵀ (ȳ/z) = ν̄ (ȳ/z)` for every `z`. -/
@[tmio T, powerlib_foundation] theorem transpose_mulVec_conj_div {A : Matrix (Fin n) (Fin n) ℝ}
    {y : Fin n → ℂ} {z ν : ℂ} (h : (Linear.complexify A)ᵀ *ᵥ y = ν • y) :
    (Linear.complexify A)ᵀ *ᵥ (fun j => starRingEnd ℂ (y j) / z) =
      starRingEnd ℂ ν • (fun j => starRingEnd ℂ (y j) / z) := by
  ext j
  have hj := congrArg (starRingEnd ℂ) (congrFun h j)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Matrix.transpose_apply, Linear.complexify, Matrix.map_apply, Complex.coe_algebraMap,
    Complex.conj_ofReal] at hj ⊢
  rw [show (∑ i, (A i j : ℂ) * (starRingEnd ℂ (y i) / z)) =
      (∑ i, (A i j : ℂ) * starRingEnd ℂ (y i)) / z by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, hj]
  ring

/-- **The root of a linear factor**: a root of `s + λ` with `λ > 0` has negative real part. -/
@[tmio T, powerlib_foundation] theorem re_neg_of_eval_X_add_C {l : ℝ} (hl : 0 < l) (s : ℂ)
    (hs : (Polynomial.X + Polynomial.C (l : ℂ)).eval s = 0) : s.re < 0 := by
  simp only [eval_add, eval_X, eval_C] at hs
  have : s = -(l : ℂ) := by linear_combination hs
  rw [this]; simp; exact hl

end powerlib.NormalForm.LyapunovCoefficient
