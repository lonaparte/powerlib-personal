import theorem.NormalForm.Hopf
import theorem.Dynamics.Degenerate.WeakFocus

/-! # The first Lyapunov coefficient of a smooth field at a Hopf equilibrium (foundation)

Kuznetsov's first Lyapunov coefficient `ℓ₁` of a field on `ℝⁿ`, defined from the field itself:
the Jacobian and the multilinear forms of the second and third derivatives at the equilibrium,
complexified, inserted into the projection formula `NormalForm.Hopf.lyap1`.

Scope.
* A field `f : State n → State n` (`State n = EuclideanSpace ℝ (Fin n)`) and a point `x₀`; the
  derivatives are Mathlib's `fderiv` and `iteratedFDeriv` (meaningful for a `C³` field, which the
  laws that need it assume). A frequency `ω₀` and complex vectors `q, p : Fin n → ℂ`; a
  *critical pair* (`IsCriticalPair`) is an equilibrium `f x₀ = 0` with `A q = iω₀ q`,
  `Aᵀ p = −iω₀ p`, `⟨p, q⟩ = 1`, `ω₀ > 0`, `A` the Jacobian. Nothing here describes a
  physical system; every statement is a generic identity or implication, a foundation result.
  Model families compute `ℓ₁` of their fields with these laws
  (`theorem/GridTiedConverter/GFM/HopfCoefficient.lean`,
  `theorem/GridTiedConverter/GFM/HopfCoefficientLine.lean`).
* The value `ℓ₁` is a static quantity of the field at a point. Its dynamical meaning (the radial
  rate `ṙ = μ r + ℓ₁ r³` of the normal form, `theorem/NormalForm/Hopf.lean`) is used here only
  through the two normal forms whose Lyapunov and Chetaev functions the library proves
  (`theorem/Dynamics/Degenerate/WeakFocus.lean`); no centre-manifold theorem is used or claimed.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 eq. (3.20) and §5.4
eq. (5.39) (`ℓ₁ = Re(⟨p, C(q, q, q̄)⟩ − 2⟨p, B(q, A⁻¹B(q, q̄))⟩ +
⟨p, B(q̄, (2iω₀ − A)⁻¹B(q, q))⟩)/(2ω₀)`); study note `gfm/t3-bifurcation/REPORT-coord.md` (c)
and its scripts `lyap.py`, `s3_hopf_l1.py` (discovery evidence only).

Results.
* Definitions: the basis vectors `basisVec`, the complexified matrix `cmat` of a real linear map,
  the complexified Jacobian `jacobianC`, the coefficients `hess`, `third` of `iteratedFDeriv ℝ 2`
  and `iteratedFDeriv ℝ 3`, their complex multilinear extensions `bilinC`, `trilinC`, the pairing
  `⟨p, x⟩ = Σ p̄ₖ xₖ` (`pairing`), and `firstLyapunov f x₀ ω₀ q p`, which is
  `NormalForm.Hopf.lyap1` of these data (the projection formula is defined once, there).
* Computation (`firstLyapunov_eq_of_solve`): when `A` and `2iω₀ − A` are invertible and
  `A r = B(q, q̄)`, `(2iω₀ − A) s = B(q, q)`, `ℓ₁` is the formula with `r` and `s`.
* Normalisation: rescaling `q ↦ s q`, `p ↦ p/s̄` keeps a critical pair critical
  (`isCriticalPair_smul`) and multiplies `ℓ₁` by `|s|²` (`firstLyapunov_smul`, read from
  `NormalForm.Hopf.lyap1_scale`). When the eigenvalue `iω₀` has one-dimensional right and left
  eigenspaces, any two critical pairs are so related (`exists_smul_of_isCriticalPair`), so the
  sign of `ℓ₁` does not depend on the normalisation (`sign_firstLyapunov_eq`).
* Translation (`firstLyapunov_comp_add`, `isCriticalPair_comp_add`, `jacobianC_comp_add`): `ℓ₁`
  and the critical pairs of `z ↦ f(z + x₀)` at `0` are those of `f` at `x₀`.
* Linear coordinates (`firstLyapunov_conj`): for a linear isomorphism `T`, `ℓ₁` of
  `y ↦ T f(T⁻¹ y)` at `T x₀` with `(T q, T⁻ᵀ p)` equals `ℓ₁` of `f` at `x₀` with `(q, p)`, and
  critical pairs correspond (`isCriticalPair_conj`). The abstract form is `lyap1_conj`.
* One-nonlinearity fields `f x = L x + c + φ(ℓ x) v` (`ridge`, `φ` of class `C³`): the Jacobian
  `L + φ'(ℓ x₀) v ℓ` (`jacobianC_ridge`), the forms `φ''(ℓ x₀) ℓ(u) ℓ(w) v` and
  `φ'''(ℓ x₀) ℓ(u) ℓ(w) ℓ(z) v` (`bilinC_ridge`, `trilinC_ridge`), and the closed form
  `ℓ₁ = Re(⟨p, v⟩ ℓ(q)² ℓ(q̄) (φ''' − 2φ''² ℓ(r) + φ''² ℓ(s)))/(2ω₀)` with `A r = v`,
  `(2iω₀ − A) s = v` (`firstLyapunov_ridge`).
* Computation from explicit derivatives (`hess_eq_of_hasFDerivAt`, `third_eq_of_hasFDerivAt`):
  the coefficients from a derivative `L₁` of `f` and the derivatives of its columns; additivity
  (`hess_add`, `third_add`, `bilinC_add`, `trilinC_add`); products `φ(ℓ x) m(x) v` of a
  nonlinearity and a linear functional (`prodRidge`, `hess_prodRidge`, `third_prodRidge`,
  `bilinC_prodRidge`, `trilinC_prodRidge`), the bilinear terms of line models.
* Relation to the library's weak-focus laws (`theorem/Dynamics/Degenerate/WeakFocus.lean`).
  Planar sine–Liénard field (`sineLienardField`, the normal form of
  `Dynamics.Degenerate.localAsymptoticStable_of_sineLienard`): at the critical pair
  `sineLienardQ`, `sineLienardP` with `ω₀ = √(αA)`, `ℓ₁ = −(4/ω₀) κ`, `κ = hopfκ A B β`
  (`firstLyapunov_sineLienard`); hence `ℓ₁ < 0` gives local asymptotic stability and `ℓ₁ > 0`
  instability, for every critical pair (`localAsymptoticStable_of_firstLyapunov_neg`,
  `unstable_of_firstLyapunov_pos`). Three-state weak focus (`weakFocusField`,
  `ȧ = b, ḃ = −H a − G, ċ = −λ c − G`, `G = g₂ ξ² + g₃ ξ³`): at `weakFocusQ`, `weakFocusP`,
  `ℓ₁ = −κ/(2λω₀³(λ² + ω₀²)²(λ² + 4ω₀²))`, `κ = hopfCoeff H λ g₂ g₃`, `ω₀² = H`
  (`firstLyapunov_weakFocus`); hence a field in the hypotheses of
  `Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus` whose cubic normal form has
  `ℓ₁ < 0` is locally asymptotically stable (`localAsymptoticStable_of_weakFocus_firstLyapunov`).
-/

noncomputable section
namespace powerlib.NormalForm.LyapunovCoefficient
open Complex Matrix
open powerlib.Dynamics (State)

/-! ## Definitions -/

variable {n : ℕ}

/-- The `j`-th standard basis vector `e_j` of `State n`. -/
def basisVec (j : Fin n) : State n := EuclideanSpace.single j 1

/-- A real vector read as a complex vector. -/
def toC (a : State n) : Fin n → ℂ := fun k => (a k : ℂ)

/-- The complexified matrix `(L e_j)_k` of a real linear map. -/
def cmat (L : State n →L[ℝ] State n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k j => (L (basisVec j) k : ℂ)

/-- The complexified Jacobian `A_{kj} = ∂f_k/∂x_j (x₀)`. -/
def jacobianC (f : State n → State n) (x₀ : State n) : Matrix (Fin n) (Fin n) ℂ :=
  cmat (fderiv ℝ f x₀)

/-- The coefficients `b_{kij} = ∂²f_k/∂x_i∂x_j (x₀)` of the second derivative
`iteratedFDeriv ℝ 2 f x₀`. -/
def hess (f : State n → State n) (x₀ : State n) (k i j : Fin n) : ℝ :=
  iteratedFDeriv ℝ 2 f x₀ ![basisVec i, basisVec j] k

/-- The coefficients `c_{kijl} = ∂³f_k/∂x_i∂x_j∂x_l (x₀)` of the third derivative
`iteratedFDeriv ℝ 3 f x₀`. -/
def third (f : State n → State n) (x₀ : State n) (k i j l : Fin n) : ℝ :=
  iteratedFDeriv ℝ 3 f x₀ ![basisVec i, basisVec j, basisVec l] k

/-- The complex bilinear extension `B(u, w)_k = Σ_{i,j} b_{kij} u_i w_j` of the second
derivative. -/
def bilinC (f : State n → State n) (x₀ : State n) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ∑ i, (LinearMap.proj i).smulRight
    (Matrix.mulVecLin (Matrix.of fun k j => (hess f x₀ k i j : ℂ)))

/-- The complex trilinear extension `C(u, w, z)_k = Σ_{i,j,l} c_{kijl} u_i w_j z_l` of the
third derivative. -/
def trilinC (f : State n → State n) (x₀ : State n) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ∑ i, (LinearMap.proj i).smulRight
    (∑ j, (LinearMap.proj j).smulRight
      (Matrix.mulVecLin (Matrix.of fun k l => (third f x₀ k i j l : ℂ))))

/-- The pairing `⟨p, x⟩ = Σ_k p̄_k x_k`. -/
def pairing (p : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  ∑ k, (starRingEnd ℂ (p k)) • LinearMap.proj k

/-- The shifted matrix `2iω₀ − A` of the second resolvent. -/
def shift2 (A : Matrix (Fin n) (Fin n) ℂ) (ω₀ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ((2 * ω₀ : ℂ) * I) • (1 : Matrix (Fin n) (Fin n) ℂ) - A

/-- **Kuznetsov's first Lyapunov coefficient** of `f` at `x₀` with frequency `ω₀` and vectors
`q, p`: the projection formula `NormalForm.Hopf.lyap1` with `B`, `C` the complexified second and
third derivatives, the resolvents `A⁻¹` and `(2iω₀ − A)⁻¹` of the complexified Jacobian, the
pairing with `p` and `q̄ = star q`. -/
def firstLyapunov (f : State n → State n) (x₀ : State n) (ω₀ : ℝ) (q p : Fin n → ℂ) : ℝ :=
  Hopf.lyap1 (bilinC f x₀) (trilinC f x₀) (jacobianC f x₀)⁻¹.mulVecLin
    (shift2 (jacobianC f x₀) ω₀)⁻¹.mulVecLin (pairing p) ω₀ q (star q)

/-- A critical pair at a Hopf equilibrium: `f x₀ = 0`, `ω₀ > 0`, `A q = iω₀ q`,
`Aᵀ p = −iω₀ p` and `⟨p, q⟩ = 1`, `A` the complexified Jacobian (so `±iω₀` are eigenvalues). -/
structure IsCriticalPair (f : State n → State n) (x₀ : State n) (ω₀ : ℝ) (q p : Fin n → ℂ) :
    Prop where
  /-- `x₀` is an equilibrium. -/
  equilibrium : f x₀ = 0
  /-- The frequency is positive. -/
  freq_pos : 0 < ω₀
  /-- `q` is a right eigenvector of `iω₀`. -/
  right : jacobianC f x₀ *ᵥ q = ((ω₀ : ℂ) * I) • q
  /-- `p` is an eigenvector of `Aᵀ` for `−iω₀`. -/
  left : (jacobianC f x₀)ᵀ *ᵥ p = (-((ω₀ : ℂ) * I)) • p
  /-- `⟨p, q⟩ = 1`. -/
  normalized : star p ⬝ᵥ q = 1

/-! ## Evaluation -/

@[tmio T, simp, powerlib_foundation] theorem pairing_apply (p x : Fin n → ℂ) :
    pairing p x = ∑ k, starRingEnd ℂ (p k) * x k := by
  simp [pairing, LinearMap.sum_apply]

@[tmio T, powerlib_foundation] theorem pairing_eq_dotProduct (p x : Fin n → ℂ) :
    pairing p x = star p ⬝ᵥ x := by
  simp [pairing_apply, dotProduct]

@[tmio T, powerlib_foundation] theorem bilinC_apply (f : State n → State n) (x₀ : State n)
    (u w : Fin n → ℂ) (k : Fin n) :
    bilinC f x₀ u w k = ∑ i, ∑ j, (hess f x₀ k i j : ℂ) * u i * w j := by
  simp only [bilinC, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[tmio T, powerlib_foundation] theorem trilinC_apply (f : State n → State n) (x₀ : State n)
    (u w z : Fin n → ℂ) (k : Fin n) :
    trilinC f x₀ u w z k = ∑ i, ∑ j, ∑ l, (third f x₀ k i j l : ℂ) * u i * w j * z l := by
  simp only [trilinC, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Computation.** If `A` and `2iω₀ − A` are invertible, `A r = B(q, q̄)` and
`(2iω₀ − A) s = B(q, q)`, then `ℓ₁ = Re(⟨p, C(q, q, q̄)⟩ − 2⟨p, B(q, r)⟩ + ⟨p, B(q̄, s)⟩)/(2ω₀)`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_eq_of_solve {f : State n → State n}
    {x₀ : State n} {ω₀ : ℝ} {q p r s : Fin n → ℂ} (hA : IsUnit (jacobianC f x₀).det)
    (h2 : IsUnit (shift2 (jacobianC f x₀) ω₀).det)
    (hr : jacobianC f x₀ *ᵥ r = bilinC f x₀ q (star q))
    (hs : shift2 (jacobianC f x₀) ω₀ *ᵥ s = bilinC f x₀ q q) :
    firstLyapunov f x₀ ω₀ q p = 1 / (2 * ω₀) *
      (pairing p (trilinC f x₀ q q (star q)) - 2 * pairing p (bilinC f x₀ q r) +
        pairing p (bilinC f x₀ (star q) s)).re := by
  have e1 : (jacobianC f x₀)⁻¹ *ᵥ bilinC f x₀ q (star q) = r := by
    rw [← hr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  have e2 : (shift2 (jacobianC f x₀) ω₀)⁻¹ *ᵥ bilinC f x₀ q q = s := by
    rw [← hs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h2, Matrix.one_mulVec]
  simp only [firstLyapunov, Hopf.lyap1, Matrix.mulVecLin_apply, e1, e2]

/-! ## Normalisation of the eigenvectors -/

@[tmio T, powerlib_foundation] private theorem pairing_smul (p : Fin n → ℂ) (s : ℂ) :
    pairing ((starRingEnd ℂ s)⁻¹ • p) = s⁻¹ • pairing p := by
  refine LinearMap.ext fun x => ?_
  simp only [pairing_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    Complex.conj_conj, LinearMap.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Scaling.** `q ↦ s q`, `p ↦ p/s̄` (`s ≠ 0`) multiplies `ℓ₁` by `|s|²`
(`NormalForm.Hopf.lyap1_scale`). -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_smul (f : State n → State n)
    (x₀ : State n) (ω₀ : ℝ) (q p : Fin n → ℂ) {s : ℂ} (hs : s ≠ 0) :
    firstLyapunov f x₀ ω₀ (s • q) ((starRingEnd ℂ s)⁻¹ • p) =
      ‖s‖ ^ 2 * firstLyapunov f x₀ ω₀ q p := by
  have hq : star (s • q) = starRingEnd ℂ s • star q := by
    ext k; simp
  simp only [firstLyapunov]
  rw [pairing_smul, hq]
  exact Hopf.lyap1_scale _ _ _ _ _ _ _ _ hs

/-- The rescaled pair `(s q, p/s̄)` of a critical pair is critical. -/
@[tmio T, powerlib_foundation] theorem isCriticalPair_smul {f : State n → State n}
    {x₀ : State n} {ω₀ : ℝ} {q p : Fin n → ℂ} (h : IsCriticalPair f x₀ ω₀ q p) {s : ℂ}
    (hs : s ≠ 0) : IsCriticalPair f x₀ ω₀ (s • q) ((starRingEnd ℂ s)⁻¹ • p) := by
  refine ⟨h.equilibrium, h.freq_pos, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, h.right, smul_comm]
  · rw [Matrix.mulVec_smul, h.left, smul_comm]
  · have hn := h.normalized
    have e : star ((starRingEnd ℂ s)⁻¹ • p) = s⁻¹ • star p := by
      ext k; simp
    rw [e, smul_dotProduct, dotProduct_smul, hn, smul_eq_mul, smul_eq_mul, mul_one,
      inv_mul_cancel₀ hs]

/-- **Independence of the normalisation.** If the right eigenspace of `iω₀` is spanned by `q` and
the left one by `p`, every critical pair `(q', p')` is `(s q, p/s̄)` with `s ≠ 0`, and its `ℓ₁` is
`|s|²` times that of `(q, p)`. -/
@[tmio T, powerlib_foundation] theorem exists_smul_of_isCriticalPair {f : State n → State n}
    {x₀ : State n} {ω₀ : ℝ} {q p q' p' : Fin n → ℂ}
    (hq : ∀ v, jacobianC f x₀ *ᵥ v = ((ω₀ : ℂ) * I) • v → ∃ c : ℂ, v = c • q)
    (hp : ∀ v, (jacobianC f x₀)ᵀ *ᵥ v = (-((ω₀ : ℂ) * I)) • v → ∃ c : ℂ, v = c • p)
    (h : IsCriticalPair f x₀ ω₀ q p) (h' : IsCriticalPair f x₀ ω₀ q' p') :
    ∃ s : ℂ, s ≠ 0 ∧ q' = s • q ∧ p' = (starRingEnd ℂ s)⁻¹ • p ∧
      firstLyapunov f x₀ ω₀ q' p' = ‖s‖ ^ 2 * firstLyapunov f x₀ ω₀ q p := by
  obtain ⟨s, rfl⟩ := hq q' h'.right
  obtain ⟨t, rfl⟩ := hp p' h'.left
  have hn := h'.normalized
  have e : star (t • p) = starRingEnd ℂ t • star p := by ext k; simp
  rw [e, smul_dotProduct, dotProduct_smul, h.normalized, smul_eq_mul, smul_eq_mul,
    mul_one] at hn
  have hs : s ≠ 0 := by rintro rfl; simp at hn
  have ht : t = (starRingEnd ℂ s)⁻¹ := by
    have h1 : starRingEnd ℂ t = s⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [← map_inv₀, ← h1, Complex.conj_conj]
  subst ht
  exact ⟨s, hs, rfl, rfl, firstLyapunov_smul f x₀ ω₀ q p hs⟩

/-- Under the hypotheses of `exists_smul_of_isCriticalPair`, the sign of `ℓ₁` is the same for
every critical pair. -/
@[tmio T, powerlib_foundation] theorem sign_firstLyapunov_eq {f : State n → State n}
    {x₀ : State n} {ω₀ : ℝ} {q p q' p' : Fin n → ℂ}
    (hq : ∀ v, jacobianC f x₀ *ᵥ v = ((ω₀ : ℂ) * I) • v → ∃ c : ℂ, v = c • q)
    (hp : ∀ v, (jacobianC f x₀)ᵀ *ᵥ v = (-((ω₀ : ℂ) * I)) • v → ∃ c : ℂ, v = c • p)
    (h : IsCriticalPair f x₀ ω₀ q p) (h' : IsCriticalPair f x₀ ω₀ q' p') :
    SignType.sign (firstLyapunov f x₀ ω₀ q' p') = SignType.sign (firstLyapunov f x₀ ω₀ q p) := by
  obtain ⟨s, hs, -, -, he⟩ := exists_smul_of_isCriticalPair hq hp h h'
  have hpos : 0 < ‖s‖ ^ 2 := by positivity
  rw [he, sign_mul, sign_pos hpos, one_mul]

/-! ## Translation -/

@[tmio T, powerlib_foundation] theorem jacobianC_comp_add (f : State n → State n)
    (x₀ : State n) : jacobianC (fun z => f (z + x₀)) 0 = jacobianC f x₀ := by
  simp only [jacobianC, fderiv_comp_add_right, zero_add]

/-- Critical pairs of `z ↦ f(z + x₀)` at `0` are those of `f` at `x₀`. -/
@[tmio T, powerlib_foundation] theorem isCriticalPair_comp_add {f : State n → State n}
    {x₀ : State n} {ω₀ : ℝ} {q p : Fin n → ℂ} :
    IsCriticalPair (fun z => f (z + x₀)) 0 ω₀ q p ↔ IsCriticalPair f x₀ ω₀ q p := by
  constructor <;> rintro ⟨h0, h1, h2, h3, h4⟩ <;>
    exact ⟨by simpa using h0, h1, by simpa [jacobianC_comp_add] using h2,
      by simpa [jacobianC_comp_add] using h3, h4⟩

/-- **Translation.** `ℓ₁` of `z ↦ f(z + x₀)` at `0` is `ℓ₁` of `f` at `x₀`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_comp_add (f : State n → State n)
    (x₀ : State n) (ω₀ : ℝ) (q p : Fin n → ℂ) :
    firstLyapunov (fun z => f (z + x₀)) 0 ω₀ q p = firstLyapunov f x₀ ω₀ q p := by
  have hJ := jacobianC_comp_add f x₀
  have hH : hess (fun z => f (z + x₀)) 0 = hess f x₀ := by
    funext k i j; simp only [hess, iteratedFDeriv_comp_add_right, zero_add]
  have hT : third (fun z => f (z + x₀)) 0 = third f x₀ := by
    funext k i j l; simp only [third, iteratedFDeriv_comp_add_right, zero_add]
  simp only [firstLyapunov, bilinC, trilinC, hJ, hH, hT]

/-! ## Real vectors and the complexification -/

@[tmio T, simp, powerlib_foundation] theorem toC_apply (a : State n) (k : Fin n) :
    toC a k = (a k : ℂ) := rfl

@[tmio T, simp, powerlib_foundation] theorem cmat_apply (L : State n →L[ℝ] State n)
    (k j : Fin n) : cmat L k j = (L (basisVec j) k : ℂ) := rfl

@[tmio T, powerlib_foundation] theorem sum_basisVec (a : State n) :
    ∑ j, a j • basisVec j = a := by
  ext k
  simp [basisVec, Pi.single_apply]

@[tmio T, powerlib_foundation] theorem toC_basisVec (j : Fin n) :
    toC (basisVec j) = Pi.single j 1 := by
  ext k
  by_cases h : k = j
  · subst h; simp [basisVec]
  · simp [basisVec, h]

@[tmio T, powerlib_foundation] theorem cmat_mulVec_toC (L : State n →L[ℝ] State n)
    (a : State n) : cmat L *ᵥ toC a = toC (L a) := by
  ext k
  conv_rhs => rw [← sum_basisVec a]
  simp [Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]

@[tmio T, powerlib_foundation] theorem matrix_ext_toC {M N : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ j, M *ᵥ toC (basisVec j) = N *ᵥ toC (basisVec j)) : M = N := by
  ext k j
  have := congrFun (h j) k
  simpa [toC_basisVec, Matrix.mulVec_single_one] using this

@[tmio T, powerlib_foundation] theorem cmat_comp (L L' : State n →L[ℝ] State n) :
    cmat (L.comp L') = cmat L * cmat L' := by
  refine matrix_ext_toC fun j => ?_
  rw [← Matrix.mulVec_mulVec, cmat_mulVec_toC, cmat_mulVec_toC, cmat_mulVec_toC]
  rfl

@[tmio T, powerlib_foundation] theorem cmat_id :
    cmat (ContinuousLinearMap.id ℝ (State n)) = 1 := by
  refine matrix_ext_toC fun j => ?_
  rw [cmat_mulVec_toC, Matrix.one_mulVec]
  rfl

@[tmio T, powerlib_foundation] theorem cmat_toEuclideanCLM (M : Matrix (Fin n) (Fin n) ℝ) :
    cmat (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) = M.map (fun x => (x : ℂ)) := by
  ext k j
  simp [Dynamics.toEuclideanCLM_apply, basisVec]

@[tmio T, powerlib_foundation] private theorem star_cmat_mulVec (L : State n →L[ℝ] State n)
    (v : Fin n → ℂ) : star (cmat L *ᵥ v) = cmat L *ᵥ star v := by
  ext k
  simp [Matrix.mulVec, dotProduct]

@[tmio T, powerlib_foundation] private theorem star_cmat_transpose_mulVec
    (L : State n →L[ℝ] State n) (v : Fin n → ℂ) :
    star ((cmat L)ᵀ *ᵥ v) = (cmat L)ᵀ *ᵥ star v := by
  ext k
  simp [Matrix.mulVec, dotProduct]

/-! ## The forms on real vectors -/

/-- The third iterated derivative as three nested Fréchet derivatives. -/
@[tmio T, powerlib_foundation] theorem iteratedFDeriv_three_apply (f : State n → State n)
    (x : State n) (m : Fin 3 → State n) :
    iteratedFDeriv ℝ 3 f x m = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x (m 0) (m 1) (m 2) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

@[tmio T, powerlib_foundation] theorem hess_eq (f : State n → State n) (x₀ : State n)
    (k i j : Fin n) :
    hess f x₀ k i j = fderiv ℝ (fderiv ℝ f) x₀ (basisVec i) (basisVec j) k := by
  simp [hess, iteratedFDeriv_two_apply]

@[tmio T, powerlib_foundation] theorem third_eq (f : State n → State n) (x₀ : State n)
    (k i j l : Fin n) :
    third f x₀ k i j l =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x₀ (basisVec i) (basisVec j) (basisVec l) k := by
  simp [third, iteratedFDeriv_three_apply]

/-- On real vectors `B` is the second derivative. -/
@[tmio T, powerlib_foundation] theorem bilinC_toC (f : State n → State n) (x₀ : State n)
    (a b : State n) :
    bilinC f x₀ (toC a) (toC b) = toC (iteratedFDeriv ℝ 2 f x₀ ![a, b]) := by
  ext k
  rw [bilinC_apply, iteratedFDeriv_two_apply]
  conv_rhs => rw [← sum_basisVec a, ← sum_basisVec b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, toC_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    smul_eq_mul, hess_eq]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- On real vectors `C` is the third derivative. -/
@[tmio T, powerlib_foundation] theorem trilinC_toC (f : State n → State n) (x₀ : State n)
    (a b c : State n) :
    trilinC f x₀ (toC a) (toC b) (toC c) = toC (iteratedFDeriv ℝ 3 f x₀ ![a, b, c]) := by
  ext k
  rw [trilinC_apply, iteratedFDeriv_three_apply]
  conv_rhs => rw [← sum_basisVec a, ← sum_basisVec b, ← sum_basisVec c]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    toC_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, third_eq]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## Linear changes of coordinates -/

/-- The derivatives of `y ↦ T f(T⁻¹ y)` (no differentiability is needed). -/
@[tmio T, powerlib_foundation] theorem iteratedFDeriv_conj (T : State n ≃L[ℝ] State n)
    (f : State n → State n) (k : ℕ) (y : State n) (m : Fin k → State n) :
    iteratedFDeriv ℝ k (fun z => T (f (T.symm z))) y m =
      T (iteratedFDeriv ℝ k f (T.symm y) (fun i => T.symm (m i))) := by
  have h1 := T.iteratedFDeriv_comp_left (f := f ∘ T.symm) (x := y) (i := k)
  have h2 := T.symm.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := y)
    (Set.mem_univ _) k
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h2
  have e : (fun z => T (f (T.symm z))) = T ∘ (f ∘ T.symm) := rfl
  rw [e, h1, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, h2]
  rfl

@[tmio T, powerlib_foundation] private theorem fderiv_conj (T : State n ≃L[ℝ] State n)
    (f : State n → State n) (x₀ : State n) :
    fderiv ℝ (fun z => T (f (T.symm z))) (T x₀) =
      (T : State n →L[ℝ] State n).comp
        ((fderiv ℝ f x₀).comp (T.symm : State n →L[ℝ] State n)) := by
  ext1 v
  have h := iteratedFDeriv_conj T f 1 (T x₀) ![v]
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply] at h
  simpa using h

/-- The Jacobian of `y ↦ T f(T⁻¹ y)` at `T x₀` is `T A T⁻¹`. -/
@[tmio T, powerlib_foundation] theorem jacobianC_conj (T : State n ≃L[ℝ] State n)
    (f : State n → State n) (x₀ : State n) :
    jacobianC (fun z => T (f (T.symm z))) (T x₀) =
      cmat (T : State n →L[ℝ] State n) * jacobianC f x₀ *
        cmat (T.symm : State n →L[ℝ] State n) := by
  rw [jacobianC, fderiv_conj, cmat_comp, cmat_comp, ← mul_assoc]
  rfl

@[tmio T, powerlib_foundation] private theorem cmat_mul_symm (T : State n ≃L[ℝ] State n) :
    cmat (T : State n →L[ℝ] State n) * cmat (T.symm : State n →L[ℝ] State n) = 1 := by
  rw [← cmat_comp, T.coe_comp_coe_symm, cmat_id]

@[tmio T, powerlib_foundation] private theorem cmat_symm_mul (T : State n ≃L[ℝ] State n) :
    cmat (T.symm : State n →L[ℝ] State n) * cmat (T : State n →L[ℝ] State n) = 1 := by
  rw [← cmat_comp, T.coe_symm_comp_coe, cmat_id]

/-- `B` of `y ↦ T f(T⁻¹ y)` at `T x₀` is `T B(T⁻¹ ·, T⁻¹ ·)`. -/
@[tmio T, powerlib_foundation] theorem bilinC_conj (T : State n ≃L[ℝ] State n)
    (f : State n → State n) (x₀ : State n) (u w : Fin n → ℂ) :
    bilinC (fun z => T (f (T.symm z))) (T x₀) (cmat (T : State n →L[ℝ] State n) *ᵥ u)
        (cmat (T : State n →L[ℝ] State n) *ᵥ w) =
      cmat (T : State n →L[ℝ] State n) *ᵥ bilinC f x₀ u w := by
  set Tc := cmat (T : State n →L[ℝ] State n)
  have key : ((bilinC (fun z => T (f (T.symm z))) (T x₀)).compl₁₂ Tc.mulVecLin
      Tc.mulVecLin) = (bilinC f x₀).compr₂ Tc.mulVecLin := by
    refine LinearMap.ext_basis (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, Matrix.mulVecLin_apply,
      Pi.basisFun_apply, ← toC_basisVec, cmat_mulVec_toC, bilinC_toC, Tc,
      ContinuousLinearEquiv.coe_coe]
    rw [iteratedFDeriv_conj]
    have e : (fun i' => T.symm (![T (basisVec i), T (basisVec j)] i')) =
        ![basisVec i, basisVec j] := by
      funext i'; fin_cases i' <;> simp
    rw [e, T.symm_apply_apply]
  have := LinearMap.congr_fun₂ key u w
  simpa using this

/-- `C` of `y ↦ T f(T⁻¹ y)` at `T x₀` is `T C(T⁻¹ ·, T⁻¹ ·, T⁻¹ ·)`. -/
@[tmio T, powerlib_foundation] theorem trilinC_conj (T : State n ≃L[ℝ] State n)
    (f : State n → State n) (x₀ : State n) (u w z : Fin n → ℂ) :
    trilinC (fun z => T (f (T.symm z))) (T x₀) (cmat (T : State n →L[ℝ] State n) *ᵥ u)
        (cmat (T : State n →L[ℝ] State n) *ᵥ w) (cmat (T : State n →L[ℝ] State n) *ᵥ z) =
      cmat (T : State n →L[ℝ] State n) *ᵥ trilinC f x₀ u w z := by
  set Tc := cmat (T : State n →L[ℝ] State n)
  have key : ∀ i j, ((trilinC (fun z => T (f (T.symm z))) (T x₀)) (Tc *ᵥ Pi.single i 1)
      (Tc *ᵥ Pi.single j 1)).comp Tc.mulVecLin =
      Tc.mulVecLin.comp (trilinC f x₀ (Pi.single i 1) (Pi.single j 1)) := by
    intro i j
    refine (Pi.basisFun ℂ (Fin n)).ext fun l => ?_
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply,
      ← toC_basisVec, cmat_mulVec_toC, trilinC_toC, Tc, ContinuousLinearEquiv.coe_coe]
    rw [iteratedFDeriv_conj]
    have e : (fun i' => T.symm (![T (basisVec i), T (basisVec j), T (basisVec l)] i')) =
        ![basisVec i, basisVec j, basisVec l] := by
      funext i'; fin_cases i' <;> simp
    rw [e, T.symm_apply_apply]
  have key2 : ((trilinC (fun z => T (f (T.symm z))) (T x₀)).compl₁₂ Tc.mulVecLin
      Tc.mulVecLin).compr₂ (LinearMap.lcomp ℂ _ Tc.mulVecLin) =
      (trilinC f x₀).compr₂ (LinearMap.llcomp ℂ _ _ _ Tc.mulVecLin) := by
    refine LinearMap.ext_basis (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) fun i j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Matrix.mulVecLin_apply,
      Pi.basisFun_apply, LinearMap.lcomp_apply']
    exact key i j
  have := LinearMap.congr_fun (LinearMap.congr_fun₂ key2 u w) z
  simpa using this

/-- **Abstract form of the coordinate invariance.** If a linear map `Φ` carries `B, C`, the
resolvents and the pairing to `B', C', …` (`B'(Φu, Φw) = Φ B(u, w)`, …, `P'(Φu) = P u`), the
projection formula takes the same value at `(Φ q, Φ q̄)` as at `(q, q̄)`. -/
@[tmio T, powerlib_foundation] theorem lyap1_conj {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (Φ : V →ₗ[ℂ] W) {B : V →ₗ[ℂ] V →ₗ[ℂ] V}
    {C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V} {Ainv R2 : V →ₗ[ℂ] V} {P : V →ₗ[ℂ] ℂ}
    {B' : W →ₗ[ℂ] W →ₗ[ℂ] W} {C' : W →ₗ[ℂ] W →ₗ[ℂ] W →ₗ[ℂ] W} {Ainv' R2' : W →ₗ[ℂ] W}
    {P' : W →ₗ[ℂ] ℂ} (hB : ∀ u w, B' (Φ u) (Φ w) = Φ (B u w))
    (hC : ∀ u w z, C' (Φ u) (Φ w) (Φ z) = Φ (C u w z)) (hA : ∀ u, Ainv' (Φ u) = Φ (Ainv u))
    (hR : ∀ u, R2' (Φ u) = Φ (R2 u)) (hP : ∀ u, P' (Φ u) = P u) (ω₀ : ℝ) {q qc : V}
    {q' qc' : W} (hq : q' = Φ q) (hqc : qc' = Φ qc) :
    Hopf.lyap1 B' C' Ainv' R2' P' ω₀ q' qc' = Hopf.lyap1 B C Ainv R2 P ω₀ q qc := by
  subst hq hqc
  simp only [Hopf.lyap1, hB, hA, hC, hR, hP]

@[tmio T, powerlib_foundation] private theorem shift2_conj (T : State n ≃L[ℝ] State n)
    (A : Matrix (Fin n) (Fin n) ℂ) (ω₀ : ℝ) :
    shift2 (cmat (T : State n →L[ℝ] State n) * A * cmat (T.symm : State n →L[ℝ] State n)) ω₀ =
      cmat (T : State n →L[ℝ] State n) * shift2 A ω₀ *
        cmat (T.symm : State n →L[ℝ] State n) := by
  simp only [shift2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, cmat_mul_symm]

@[tmio T, powerlib_foundation] private theorem inv_conj (T : State n ≃L[ℝ] State n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (cmat (T : State n →L[ℝ] State n) * A * cmat (T.symm : State n →L[ℝ] State n))⁻¹ =
      cmat (T : State n →L[ℝ] State n) * A⁻¹ * cmat (T.symm : State n →L[ℝ] State n) := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (cmat_mul_symm T),
    Matrix.inv_eq_left_inv (cmat_symm_mul T), mul_assoc]

@[tmio T, powerlib_foundation] private theorem conj_mulVec (T : State n ≃L[ℝ] State n)
    (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    (cmat (T : State n →L[ℝ] State n) * A * cmat (T.symm : State n →L[ℝ] State n)) *ᵥ
        (cmat (T : State n →L[ℝ] State n) *ᵥ u) =
      cmat (T : State n →L[ℝ] State n) *ᵥ (A *ᵥ u) := by
  rw [Matrix.mulVec_mulVec, mul_assoc, mul_assoc, cmat_symm_mul, mul_one, ← Matrix.mulVec_mulVec]

@[tmio T, powerlib_foundation] private theorem pairing_conj (T : State n ≃L[ℝ] State n)
    (p u : Fin n → ℂ) :
    pairing ((cmat (T.symm : State n →L[ℝ] State n))ᵀ *ᵥ p)
        (cmat (T : State n →L[ℝ] State n) *ᵥ u) = pairing p u := by
  rw [pairing_eq_dotProduct, pairing_eq_dotProduct, star_cmat_transpose_mulVec,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, cmat_symm_mul,
    Matrix.one_mulVec]

/-- **Invariance under linear changes of coordinates.** For a linear isomorphism `T`, `ℓ₁` of
`y ↦ T f(T⁻¹ y)` at `T x₀` with `(T q, T⁻ᵀ p)` is `ℓ₁` of `f` at `x₀` with `(q, p)`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_conj (T : State n ≃L[ℝ] State n)
    (f : State n → State n) (x₀ : State n) (ω₀ : ℝ) (q p : Fin n → ℂ) :
    firstLyapunov (fun z => T (f (T.symm z))) (T x₀) ω₀
        (cmat (T : State n →L[ℝ] State n) *ᵥ q)
        ((cmat (T.symm : State n →L[ℝ] State n))ᵀ *ᵥ p) = firstLyapunov f x₀ ω₀ q p := by
  unfold firstLyapunov
  rw [jacobianC_conj, inv_conj, shift2_conj, inv_conj]
  refine lyap1_conj (cmat (T : State n →L[ℝ] State n)).mulVecLin (fun u w => ?_)
    (fun u w z => ?_) (fun u => ?_) (fun u => ?_) (fun u => ?_) ω₀ rfl ?_
  · exact bilinC_conj T f x₀ u w
  · exact trilinC_conj T f x₀ u w z
  · simp only [Matrix.mulVecLin_apply]; exact conj_mulVec T _ u
  · simp only [Matrix.mulVecLin_apply]; exact conj_mulVec T _ u
  · simp only [Matrix.mulVecLin_apply]; exact pairing_conj T p u
  · simp only [Matrix.mulVecLin_apply]; exact star_cmat_mulVec _ q

/-- Critical pairs correspond under `T`: `(q, p) ↦ (T q, T⁻ᵀ p)`. -/
@[tmio T, powerlib_foundation] theorem isCriticalPair_conj (T : State n ≃L[ℝ] State n)
    {f : State n → State n} {x₀ : State n} {ω₀ : ℝ} {q p : Fin n → ℂ}
    (h : IsCriticalPair f x₀ ω₀ q p) :
    IsCriticalPair (fun z => T (f (T.symm z))) (T x₀) ω₀
      (cmat (T : State n →L[ℝ] State n) *ᵥ q)
      ((cmat (T.symm : State n →L[ℝ] State n))ᵀ *ᵥ p) := by
  refine ⟨by simp [h.equilibrium], h.freq_pos, ?_, ?_, ?_⟩
  · rw [jacobianC_conj, conj_mulVec, h.right, Matrix.mulVec_smul]
  · rw [jacobianC_conj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec,
      mul_assoc, mul_assoc, ← Matrix.transpose_mul, cmat_symm_mul, Matrix.transpose_one,
      mul_one, ← Matrix.mulVec_mulVec, h.left, Matrix.mulVec_smul]
  · rw [← pairing_eq_dotProduct, pairing_conj, pairing_eq_dotProduct, h.normalized]

/-! ## Fields with one nonlinearity -/

/-- The field `x ↦ L x + c + φ(ℓ x) v`: one scalar nonlinearity `φ` of one linear functional
`ℓ`, along one direction `v`. -/
def ridge (L : State n →L[ℝ] State n) (c : State n) (ℓ : State n →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (v : State n) (x : State n) : State n :=
  L x + c + φ (ℓ x) • v

/-- The complexified functional `ℓ(u) = Σ_i ℓ(e_i) u_i`. -/
def funC (ℓ : State n →L[ℝ] ℝ) (u : Fin n → ℂ) : ℂ := ∑ i, (ℓ (basisVec i) : ℂ) * u i

@[tmio T, powerlib_foundation] theorem funC_smul (ℓ : State n →L[ℝ] ℝ) (a : ℂ)
    (u : Fin n → ℂ) : funC ℓ (a • u) = a * funC ℓ u := by
  simp only [funC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

@[tmio T, simp, powerlib_foundation] theorem funC_coord (i : Fin n) (u : Fin n → ℂ) :
    funC (Dynamics.coord i) u = u i := by
  simp [funC, basisVec, apply_ite, ite_mul]

@[tmio T, powerlib_foundation] theorem funC_star (ℓ : State n →L[ℝ] ℝ) (u : Fin n → ℂ) :
    funC ℓ (star u) = starRingEnd ℂ (funC ℓ u) := by
  simp [funC, map_sum]

section Ridge

variable (L : State n →L[ℝ] State n) (c : State n) (ℓ : State n →L[ℝ] ℝ) (v : State n)
  {φ : ℝ → ℝ}

@[tmio T, powerlib_foundation] theorem contDiff_ridge (hφ : ContDiff ℝ 3 φ) :
    ContDiff ℝ 3 (ridge L c ℓ φ v) :=
  (L.contDiff.add contDiff_const).add ((hφ.comp ℓ.contDiff).smul contDiff_const)

@[tmio T, powerlib_foundation] theorem hasFDerivAt_ridge (hφ : Differentiable ℝ φ)
    (x : State n) :
    HasFDerivAt (ridge L c ℓ φ v) (L + deriv φ (ℓ x) • ℓ.smulRight v) x := by
  have h1 := (L.hasFDerivAt (x := x)).add_const c
  have h2 := ((hφ (ℓ x)).hasDerivAt.comp_hasFDerivAt x ℓ.hasFDerivAt).smul_const v
  refine (h1.add h2).congr_fderiv ?_
  ext1 w
  simp [smul_smul]

/-- The Jacobian of a one-nonlinearity field: `L + φ'(ℓ x₀) v ℓ`. -/
@[tmio T, powerlib_foundation] theorem jacobianC_ridge (hφ : Differentiable ℝ φ)
    (x₀ : State n) :
    jacobianC (ridge L c ℓ φ v) x₀ = cmat (L + deriv φ (ℓ x₀) • ℓ.smulRight v) := by
  rw [jacobianC, (hasFDerivAt_ridge L c ℓ v hφ x₀).fderiv]

/-- The second and third derivatives of a one-nonlinearity field:
`D^k f(x) m = (Π ℓ(m_i)) φ^{(k)}(ℓ x) v` (`k = 2, 3`). -/
@[tmio T, powerlib_foundation] theorem iteratedFDeriv_ridge (hφ : ContDiff ℝ 3 φ) {k : ℕ}
    (hk2 : 2 ≤ k) (hk3 : k ≤ 3) (x : State n) (m : Fin k → State n) :
    iteratedFDeriv ℝ k (ridge L c ℓ φ v) x m =
      ((∏ i, ℓ (m i)) * iteratedDeriv k φ (ℓ x)) • v := by
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk3
  have haff : ContDiff ℝ k (fun x => L x + c) := L.contDiff.add contDiff_const
  have hnl : ContDiff ℝ 3 (fun t => φ t • v) := hφ.smul contDiff_const
  have hr : ContDiff ℝ k (fun x => φ (ℓ x) • v) := (hnl.comp ℓ.contDiff).of_le hk
  have e : ridge L c ℓ φ v = (fun x => L x + c) + (fun x => φ (ℓ x) • v) := rfl
  rw [e, iteratedFDeriv_add_apply haff.contDiffAt hr.contDiffAt]
  have h0 : iteratedFDeriv ℝ k (fun x => L x + c) x = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    ext m'
    rw [iteratedFDeriv_succ_apply_right]
    have hd : (fun y => fderiv ℝ (fun x => L x + c) y) = fun _ => L := by
      funext y; exact ((L.hasFDerivAt).add_const c).fderiv
    rw [hd, iteratedFDeriv_const_of_ne (by omega)]
    simp
  have e2 : (fun x => φ (ℓ x) • v) = (fun t => φ t • v) ∘ ℓ := rfl
  rw [h0, zero_add, e2, ContinuousLinearMap.iteratedFDeriv_comp_right ℓ hnl x hk,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_smul_const_apply (hφ.contDiffAt.of_le hk)]
  simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

@[tmio T, powerlib_foundation] theorem hess_ridge (hφ : ContDiff ℝ 3 φ) (x₀ : State n)
    (k i j : Fin n) :
    hess (ridge L c ℓ φ v) x₀ k i j =
      iteratedDeriv 2 φ (ℓ x₀) * ℓ (basisVec i) * ℓ (basisVec j) * v k := by
  simp only [hess, iteratedFDeriv_ridge L c ℓ v hφ le_rfl (by norm_num), Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.smul_apply, smul_eq_mul]
  ring

@[tmio T, powerlib_foundation] theorem third_ridge (hφ : ContDiff ℝ 3 φ) (x₀ : State n)
    (k i j l : Fin n) :
    third (ridge L c ℓ φ v) x₀ k i j l =
      iteratedDeriv 3 φ (ℓ x₀) * ℓ (basisVec i) * ℓ (basisVec j) * ℓ (basisVec l) * v k := by
  simp only [third, iteratedFDeriv_ridge L c ℓ v hφ (by norm_num) le_rfl, Fin.prod_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `B(u, w) = φ''(ℓ x₀) ℓ(u) ℓ(w) v`. -/
@[tmio T, powerlib_foundation] theorem bilinC_ridge (hφ : ContDiff ℝ 3 φ) (x₀ : State n)
    (u w : Fin n → ℂ) :
    bilinC (ridge L c ℓ φ v) x₀ u w =
      (((iteratedDeriv 2 φ (ℓ x₀) : ℝ) : ℂ) * funC ℓ u * funC ℓ w) • toC v := by
  ext k
  simp only [bilinC_apply, hess_ridge L c ℓ v hφ, funC, Pi.smul_apply, toC_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `C(u, w, z) = φ'''(ℓ x₀) ℓ(u) ℓ(w) ℓ(z) v`. -/
@[tmio T, powerlib_foundation] theorem trilinC_ridge (hφ : ContDiff ℝ 3 φ) (x₀ : State n)
    (u w z : Fin n → ℂ) :
    trilinC (ridge L c ℓ φ v) x₀ u w z =
      (((iteratedDeriv 3 φ (ℓ x₀) : ℝ) : ℂ) * funC ℓ u * funC ℓ w * funC ℓ z) • toC v := by
  ext k
  simp only [trilinC_apply, third_ridge L c ℓ v hφ, funC, Pi.smul_apply, toC_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  push_cast
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **`ℓ₁` of a one-nonlinearity field.** With `A r = v`, `(2iω₀ − A) s = v`
(`A`, `2iω₀ − A` invertible),
`ℓ₁ = Re(⟨p, v⟩ ℓ(q)² ℓ(q̄) (φ''' − 2φ''² ℓ(r) + φ''² ℓ(s)))/(2ω₀)`, the derivatives at `ℓ x₀`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_ridge (hφ : ContDiff ℝ 3 φ)
    {x₀ : State n} {ω₀ : ℝ} {q p r s : Fin n → ℂ}
    (hA : IsUnit (jacobianC (ridge L c ℓ φ v) x₀).det)
    (h2 : IsUnit (shift2 (jacobianC (ridge L c ℓ φ v) x₀) ω₀).det)
    (hr : jacobianC (ridge L c ℓ φ v) x₀ *ᵥ r = toC v)
    (hs : shift2 (jacobianC (ridge L c ℓ φ v) x₀) ω₀ *ᵥ s = toC v) :
    firstLyapunov (ridge L c ℓ φ v) x₀ ω₀ q p = 1 / (2 * ω₀) *
      (pairing p (toC v) * funC ℓ q ^ 2 * starRingEnd ℂ (funC ℓ q) *
        (((iteratedDeriv 3 φ (ℓ x₀) : ℝ) : ℂ) -
          2 * ((iteratedDeriv 2 φ (ℓ x₀) : ℝ) : ℂ) ^ 2 * funC ℓ r +
          ((iteratedDeriv 2 φ (ℓ x₀) : ℝ) : ℂ) ^ 2 * funC ℓ s)).re := by
  set φ2 : ℂ := ((iteratedDeriv 2 φ (ℓ x₀) : ℝ) : ℂ)
  set a : ℂ := funC ℓ q
  have hr' : jacobianC (ridge L c ℓ φ v) x₀ *ᵥ ((φ2 * a * starRingEnd ℂ a) • r) =
      bilinC (ridge L c ℓ φ v) x₀ q (star q) := by
    rw [Matrix.mulVec_smul, hr, bilinC_ridge L c ℓ v hφ, funC_star]
  have hs' : shift2 (jacobianC (ridge L c ℓ φ v) x₀) ω₀ *ᵥ ((φ2 * a * a) • s) =
      bilinC (ridge L c ℓ φ v) x₀ q q := by
    rw [Matrix.mulVec_smul, hs, bilinC_ridge L c ℓ v hφ]
  rw [firstLyapunov_eq_of_solve hA h2 hr' hs']
  simp only [trilinC_ridge L c ℓ v hφ, bilinC_ridge L c ℓ v hφ, funC_smul, funC_star, map_smul,
    smul_eq_mul]
  congr 2
  ring

end Ridge

/-- Derivatives `φ', φ'', φ'''` from a chain of `HasDerivAt` statements. -/
@[tmio T, powerlib_foundation] theorem iteratedDeriv_of_hasDerivAt {φ φ1 φ2 φ3 : ℝ → ℝ}
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t) (t : ℝ) :
    deriv φ t = φ1 t ∧ iteratedDeriv 2 φ t = φ2 t ∧ iteratedDeriv 3 φ t = φ3 t := by
  have d1 : deriv φ = φ1 := funext fun t => (h1 t).deriv
  have d2 : deriv φ1 = φ2 := funext fun t => (h2 t).deriv
  have d3 : deriv φ2 = φ3 := funext fun t => (h3 t).deriv
  have i2 : iteratedDeriv 2 φ = φ2 := by rw [iteratedDeriv_succ, iteratedDeriv_one, d1, d2]
  refine ⟨by rw [d1], by rw [i2], ?_⟩
  rw [iteratedDeriv_succ, i2, d3]

/-! ## The planar sine–Liénard normal form -/

section SineLienard

open Dynamics.Degenerate

/-- The planar sine–Liénard field of `Dynamics.Degenerate.localAsymptoticStable_of_sineLienard`:
in the coordinates `φ = z₀`, `w = z₁ − b z₀` it reads `φ̇ = αw + βN(φ)`, `ẇ = −Aφ + N(φ)`,
`N = hopfN A B`. -/
def sineLienardField (A B α β b : ℝ) (z : State 2) : State 2 :=
  PhasePlane.mk (α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (b * (α * (z 1 - b * z 0) + β * hopfN A B (z 0)) + (-A * z 0 + hopfN A B (z 0)))

/-- The linear part of `sineLienardField`. -/
def sineLienardLin (A α b : ℝ) : State 2 →L[ℝ] State 2 :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![-(α * b), α; -(α * b ^ 2) - A, α * b]

/-- The critical right eigenvector `q = (1, b + iω₀/α)`. -/
def sineLienardQ (α b ω₀ : ℝ) : Fin 2 → ℂ := ![1, (b : ℂ) + ((ω₀ / α : ℝ) : ℂ) * I]

/-- The critical left eigenvector `p = (1/2 − iαb/(2ω₀), iα/(2ω₀))`. -/
def sineLienardP (α b ω₀ : ℝ) : Fin 2 → ℂ :=
  ![((1 / 2 : ℝ) : ℂ) - ((α * b / (2 * ω₀) : ℝ) : ℂ) * I, ((α / (2 * ω₀) : ℝ) : ℂ) * I]

@[tmio T, powerlib_foundation] theorem sineLienardField_eq_ridge (A B α β b : ℝ) :
    sineLienardField A B α β b =
      ridge (sineLienardLin A α b) 0 (Dynamics.coord 0) (hopfN A B)
        (PhasePlane.mk β (b * β + 1)) := by
  funext z
  ext i
  fin_cases i <;>
    simp [sineLienardField, sineLienardLin, ridge, Dynamics.toEuclideanCLM_apply,
      Fin.sum_univ_two] <;> ring

@[tmio T, powerlib_foundation] private theorem hopfN_derivs (A B t : ℝ) :
    deriv (hopfN A B) t = A * (1 - Real.cos t) + B * Real.sin t ∧
      iteratedDeriv 2 (hopfN A B) t = A * Real.sin t + B * Real.cos t ∧
      iteratedDeriv 3 (hopfN A B) t = A * Real.cos t - B * Real.sin t := by
  refine iteratedDeriv_of_hasDerivAt (φ1 := fun t => A * (1 - Real.cos t) + B * Real.sin t)
    (φ2 := fun t => A * Real.sin t + B * Real.cos t)
    (φ3 := fun t => A * Real.cos t - B * Real.sin t) (fun t => ?_) (fun t => ?_) (fun t => ?_) t
  · exact ((((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul A).add
      (((Real.hasDerivAt_cos t).const_sub 1).const_mul B)).congr_deriv (by simp)
  · exact ((((Real.hasDerivAt_cos t).const_sub 1).const_mul A).add
      ((Real.hasDerivAt_sin t).const_mul B)).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_sin t).const_mul A).add
      ((Real.hasDerivAt_cos t).const_mul B)).congr_deriv (by ring)

@[tmio T, powerlib_foundation] private theorem contDiff_hopfN (A B : ℝ) :
    ContDiff ℝ 3 (hopfN A B) := by
  unfold hopfN; fun_prop

@[tmio T, powerlib_foundation] private theorem sineLienard_jacobianC (A B α β b : ℝ) :
    jacobianC (sineLienardField A B α β b) 0 =
      (!![-(α * b), α; -(α * b ^ 2) - A, α * b] : Matrix (Fin 2) (Fin 2) ℝ).map
        (fun x => (x : ℂ)) := by
  rw [sineLienardField_eq_ridge, jacobianC_ridge _ _ _ _
    ((contDiff_hopfN A B).differentiable (by norm_num)) 0, (hopfN_derivs A B _).1]
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [sineLienardLin, basisVec, Dynamics.toEuclideanCLM_apply]

/-- The data of `sineLienardField` at its Hopf point, with `ω₀² = αA`. -/
@[tmio T, powerlib_foundation] private theorem sineLienard_data {A B α β b ω₀ : ℝ}
    (hα : α ≠ 0) (hω : 0 < ω₀) (hαA : α * A = ω₀ ^ 2) :
    IsCriticalPair (sineLienardField A B α β b) 0 ω₀ (sineLienardQ α b ω₀)
        (sineLienardP α b ω₀) ∧
      firstLyapunov (sineLienardField A B α β b) 0 ω₀ (sineLienardQ α b ω₀)
        (sineLienardP α b ω₀) = -(4 / ω₀) * hopfκ A B β := by
  obtain rfl : A = ω₀ ^ 2 / α := by field_simp; linarith
  have hω0 : ω₀ ≠ 0 := hω.ne'
  have hJ := sineLienard_jacobianC (ω₀ ^ 2 / α) B α β b
  refine ⟨⟨?_, hω, ?_, ?_, ?_⟩, ?_⟩
  · ext i; fin_cases i <;> simp [sineLienardField, hopfN]
  · rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sineLienardQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp <;> ring)
  · rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sineLienardP, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp <;> ring)
  · simp [dotProduct, Fin.sum_univ_two, sineLienardP, sineLienardQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; ring)
  set r : Fin 2 → ℂ := ![((-α / ω₀ ^ 2 : ℝ) : ℂ), (((ω₀ ^ 2 / α * β - α * b) / ω₀ ^ 2 : ℝ) : ℂ)]
  set s : Fin 2 → ℂ := ![((-α / (3 * ω₀ ^ 2) : ℝ) : ℂ) + ((-2 * β / (3 * ω₀) : ℝ) : ℂ) * I,
    (((ω₀ ^ 2 / α * β - α * b) / (3 * ω₀ ^ 2) : ℝ) : ℂ) +
      ((-2 * (b * β + 1) / (3 * ω₀) : ℝ) : ℂ) * I]
  have hdet : (jacobianC (sineLienardField (ω₀ ^ 2 / α) B α β b) 0).det =
      ((ω₀ ^ 2 : ℝ) : ℂ) := by
    rw [hJ, Matrix.det_fin_two]
    simp [Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (field_simp; ring)
  have hdet2 : (shift2 (jacobianC (sineLienardField (ω₀ ^ 2 / α) B α β b) 0) ω₀).det =
      ((-3 * ω₀ ^ 2 : ℝ) : ℂ) := by
    rw [hJ, shift2, Matrix.det_fin_two]
    simp [Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; ring)
  have hr : jacobianC (sineLienardField (ω₀ ^ 2 / α) B α β b) 0 *ᵥ r =
      toC (PhasePlane.mk β (b * β + 1)) := by
    rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, r, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (field_simp; ring)
  have hs : shift2 (jacobianC (sineLienardField (ω₀ ^ 2 / α) B α β b) 0) ω₀ *ᵥ s =
      toC (PhasePlane.mk β (b * β + 1)) := by
    rw [hJ, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, s, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; ring)
  have hu1 := hdet ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hω0))
  have hu2 := hdet2 ▸ isUnit_iff_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (by nlinarith [pow_pos hω 2] : -3 * ω₀ ^ 2 < 0).ne)
  rw [sineLienardField_eq_ridge] at hu1 hu2 hr hs ⊢
  rw [firstLyapunov_ridge _ _ _ _ (contDiff_hopfN _ B) hu1 hu2 hr hs]
  obtain ⟨-, h2, h3⟩ := hopfN_derivs (ω₀ ^ 2 / α) B 0
  simp only [map_zero, h2, h3, Real.sin_zero, Real.cos_zero]
  simp [funC, pairing_apply, Fin.sum_univ_two, basisVec, sineLienardQ, sineLienardP, r, s,
    hopfκ, Complex.mul_re, Complex.mul_im, pow_two, -Complex.ofReal_mul, -Complex.ofReal_div,
    -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add,
    -Complex.ofReal_inv]
  field_simp
  ring

end SineLienard

section SineLienardLaws

open Dynamics.Degenerate

@[tmio T, powerlib_foundation] private theorem sineLienard_spans {A B α β b ω₀ : ℝ}
    (hα : α ≠ 0) (hω : 0 < ω₀) :
    (∀ v, jacobianC (sineLienardField A B α β b) 0 *ᵥ v = ((ω₀ : ℂ) * I) • v →
      ∃ c : ℂ, v = c • sineLienardQ α b ω₀) ∧
    (∀ v, (jacobianC (sineLienardField A B α β b) 0)ᵀ *ᵥ v = (-((ω₀ : ℂ) * I)) • v →
      ∃ c : ℂ, v = c • sineLienardP α b ω₀) := by
  have hJ := sineLienard_jacobianC A B α β b
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  have hω' : (ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  constructor
  · intro v hv
    have h0 := congrFun hv 0
    rw [hJ] at h0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i
    · simp [sineLienardQ]
    · simp [sineLienardQ]
      field_simp
      linear_combination h0
  · intro v hv
    have h1 := congrFun hv 1
    rw [hJ] at h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    refine ⟨((-2 * ω₀ / α : ℝ) : ℂ) * I * v 1, ?_⟩
    ext i; fin_cases i
    · simp [sineLienardP]
      field_simp
      linear_combination h1 + (-(α : ℂ) * b * v 1) * Complex.I_sq
    · simp [sineLienardP]
      field_simp
      linear_combination v 1 * Complex.I_sq

end SineLienardLaws

section SineLienardPublic

open Dynamics.Degenerate

@[tmio T, powerlib_foundation] private theorem sineLienard_freq {A α : ℝ} (hA : A ≠ 0)
    (hq : 0 < α / A) : α ≠ 0 ∧ 0 < √(α * A) ∧ α * A = √(α * A) ^ 2 := by
  have hαA : 0 < α * A := by
    have h := mul_pos hq (pow_pos (abs_pos.mpr hA) 2)
    rwa [sq_abs, show α / A * A ^ 2 = α * A by field_simp] at h
  refine ⟨fun h => by simp [h] at hq, Real.sqrt_pos.mpr hαA, (Real.sq_sqrt hαA.le).symm⟩

/-- The critical pair of the sine–Liénard field at `ω₀ = √(αA)`. -/
@[tmio T, powerlib_foundation] theorem isCriticalPair_sineLienard {A B α β b : ℝ} (hA : A ≠ 0)
    (hq : 0 < α / A) :
    IsCriticalPair (sineLienardField A B α β b) 0 √(α * A) (sineLienardQ α b √(α * A))
      (sineLienardP α b √(α * A)) :=
  let ⟨hα, hω, hαA⟩ := sineLienard_freq hA hq
  (sineLienard_data hα hω hαA).1

/-- **`ℓ₁` of the sine–Liénard field**: `ℓ₁ = −(4/ω₀) κ`, `κ = −β(A² + B²)/(16A)` (`hopfκ`),
`ω₀ = √(αA)`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_sineLienard {A B α β b : ℝ} (hA : A ≠ 0)
    (hq : 0 < α / A) :
    firstLyapunov (sineLienardField A B α β b) 0 √(α * A) (sineLienardQ α b √(α * A))
      (sineLienardP α b √(α * A)) = -(4 / √(α * A)) * hopfκ A B β :=
  let ⟨hα, hω, hαA⟩ := sineLienard_freq hA hq
  (sineLienard_data hα hω hαA).2

@[tmio T, powerlib_foundation] private theorem sineLienard_field_eq {A B α β b : ℝ}
    {g : State 2 → State 2}
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) :
    g = sineLienardField A B α β b := by
  funext z
  ext i
  fin_cases i
  · simp [sineLienardField, hg0 z]
  · have h := hg1 z
    rw [hg0 z] at h
    simp [sineLienardField]
    linarith

@[tmio T, powerlib_foundation] private theorem sineLienard_sign {A B α β b : ℝ} (hA : A ≠ 0)
    (hq : 0 < α / A) {q p : Fin 2 → ℂ}
    (hc : IsCriticalPair (sineLienardField A B α β b) 0 √(α * A) q p) :
    SignType.sign (firstLyapunov (sineLienardField A B α β b) 0 √(α * A) q p) =
      SignType.sign (-(4 / √(α * A)) * hopfκ A B β) := by
  obtain ⟨hα, hω, -⟩ := sineLienard_freq hA hq
  obtain ⟨h1, h2⟩ := sineLienard_spans (A := A) (B := B) (β := β) (b := b) hα hω
  rw [sign_firstLyapunov_eq h1 h2 (isCriticalPair_sineLienard hA hq) hc,
    firstLyapunov_sineLienard hA hq]

/-- **Planar weak focus from `ℓ₁ < 0`.** A `C¹` field in the sine–Liénard normal form of
`Dynamics.Degenerate.localAsymptoticStable_of_sineLienard` whose first Lyapunov coefficient at
the origin, for some critical pair, is negative is locally asymptotically stable. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_firstLyapunov_neg
    {A B α β b : ℝ} (hA : A ≠ 0) (hq : 0 < α / A) {g : State 2 → State 2}
    (hgc : ContDiff ℝ 1 g)
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) {q p : Fin 2 → ℂ}
    (hc : IsCriticalPair g 0 √(α * A) q p) (hl : firstLyapunov g 0 √(α * A) q p < 0) :
    LocalAsymptoticStable g 0 := by
  obtain ⟨hα, hω, -⟩ := sineLienard_freq hA hq
  have hgf := sineLienard_field_eq hg0 hg1
  rw [hgf] at hc hl
  have hs := sineLienard_sign hA hq hc
  rw [sign_neg hl, eq_comm, sign_eq_neg_one_iff] at hs
  have hκ : 0 < hopfκ A B β := by
    have h4 : 0 < 4 / √(α * A) := by positivity
    nlinarith
  exact localAsymptoticStable_of_sineLienard hA hα hq hκ hgc hg0 hg1

/-- **Planar unstable focus from `ℓ₁ > 0`.** A `C¹` field in the sine–Liénard normal form whose
first Lyapunov coefficient at the origin, for some critical pair, is positive is unstable
(`Dynamics.Degenerate.unstable_of_sineLienard`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_firstLyapunov_pos
    {A B α β b : ℝ} (hA : A ≠ 0) (hq : 0 < α / A) {g : State 2 → State 2}
    (hgc : ContDiff ℝ 1 g)
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) {q p : Fin 2 → ℂ}
    (hc : IsCriticalPair g 0 √(α * A) q p) (hl : 0 < firstLyapunov g 0 √(α * A) q p) :
    Unstable g 0 := by
  obtain ⟨hα, hω, -⟩ := sineLienard_freq hA hq
  have hgf := sineLienard_field_eq hg0 hg1
  rw [hgf] at hc hl
  have hs := sineLienard_sign hA hq hc
  rw [sign_pos hl, eq_comm, sign_eq_one_iff] at hs
  have hκ : hopfκ A B β < 0 := by
    have h4 : 0 < 4 / √(α * A) := by positivity
    nlinarith
  exact unstable_of_sineLienard hA hα hq hκ hgc hg0 hg1

end SineLienardPublic

/-! ## The three-state weak-focus normal form -/

section WeakFocus

open Dynamics.Degenerate

/-- The cubic forcing `G(ξ) = g₂ ξ² + g₃ ξ³`. -/
def weakFocusG (g2 g3 s : ℝ) : ℝ := g2 * s ^ 2 + g3 * s ^ 3

/-- The forcing coordinate `ξ = (λ a − b + c)/(H + λ²)`. -/
def weakFocusXi (H lam : ℝ) : State 3 →L[ℝ] ℝ :=
  (lam / (H + lam ^ 2)) • Dynamics.coord 0 - (1 / (H + lam ^ 2)) • Dynamics.coord 1 +
    (1 / (H + lam ^ 2)) • Dynamics.coord 2

/-- The linear part of the weak-focus normal form. -/
def weakFocusLin (H lam : ℝ) : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) !![0, 1, 0; -H, 0, 0; 0, 0, -lam]

/-- The cubic weak-focus normal form of
`Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus`, `w = (a, b, c)`:
`ȧ = b`, `ḃ = −H a − G(ξ)`, `ċ = −λ c − G(ξ)`. -/
def weakFocusField (H lam g2 g3 : ℝ) (w : State 3) : State 3 :=
  Dynamics.mk3 (w 1)
    (-H * w 0 - weakFocusG g2 g3 ((lam * w 0 - w 1 + w 2) / (H + lam ^ 2)))
    (-lam * w 2 - weakFocusG g2 g3 ((lam * w 0 - w 1 + w 2) / (H + lam ^ 2)))

/-- The critical right eigenvector `q = (1, iω₀, 0)`. -/
def weakFocusQ (ω₀ : ℝ) : Fin 3 → ℂ := ![1, (ω₀ : ℂ) * I, 0]

/-- The critical left eigenvector `p = (1/2, i/(2ω₀), 0)`. -/
def weakFocusP (ω₀ : ℝ) : Fin 3 → ℂ := ![((1 / 2 : ℝ) : ℂ), ((1 / (2 * ω₀) : ℝ) : ℂ) * I, 0]

@[tmio T, powerlib_foundation] theorem weakFocusField_eq_ridge (H lam g2 g3 : ℝ) :
    weakFocusField H lam g2 g3 =
      ridge (weakFocusLin H lam) 0 (weakFocusXi H lam) (weakFocusG g2 g3)
        (Dynamics.mk3 0 (-1) (-1)) := by
  funext w
  have hx : weakFocusXi H lam w = (lam * w 0 - w 1 + w 2) / (H + lam ^ 2) := by
    simp only [weakFocusXi, _root_.add_apply, _root_.sub_apply,
      _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul]
    ring
  apply Dynamics.state3_ext <;>
    simp [weakFocusField, weakFocusLin, ridge, Dynamics.toEuclideanCLM_apply3, hx] <;> ring

@[tmio T, powerlib_foundation] private theorem weakFocusG_derivs (g2 g3 t : ℝ) :
    deriv (weakFocusG g2 g3) t = 2 * g2 * t + 3 * g3 * t ^ 2 ∧
      iteratedDeriv 2 (weakFocusG g2 g3) t = 2 * g2 + 6 * g3 * t ∧
      iteratedDeriv 3 (weakFocusG g2 g3) t = 6 * g3 := by
  refine iteratedDeriv_of_hasDerivAt (φ1 := fun t => 2 * g2 * t + 3 * g3 * t ^ 2)
    (φ2 := fun t => 2 * g2 + 6 * g3 * t) (φ3 := fun _ => 6 * g3) (fun t => ?_) (fun t => ?_)
    (fun t => ?_) t
  · exact ((((hasDerivAt_id t).pow 2).const_mul g2).add
      (((hasDerivAt_id t).pow 3).const_mul g3)).congr_deriv (by simp; ring)
  · exact ((((hasDerivAt_id t).const_mul (2 * g2))).add
      (((hasDerivAt_id t).pow 2).const_mul (3 * g3))).congr_deriv (by simp; ring)
  · exact ((hasDerivAt_const t (2 * g2)).add
      ((hasDerivAt_id t).const_mul (6 * g3))).congr_deriv (by simp)

@[tmio T, powerlib_foundation] private theorem contDiff_weakFocusG (g2 g3 : ℝ) :
    ContDiff ℝ 3 (weakFocusG g2 g3) := by
  unfold weakFocusG; fun_prop

@[tmio T, powerlib_foundation] private theorem weakFocus_jacobianC (H lam g2 g3 : ℝ) :
    jacobianC (weakFocusField H lam g2 g3) 0 =
      (!![0, 1, 0; -H, 0, 0; 0, 0, -lam] : Matrix (Fin 3) (Fin 3) ℝ).map
        (fun x => (x : ℂ)) := by
  rw [weakFocusField_eq_ridge, jacobianC_ridge _ _ _ _
    ((contDiff_weakFocusG g2 g3).differentiable (by norm_num)) 0,
    (weakFocusG_derivs g2 g3 _).1]
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [weakFocusLin, basisVec, Dynamics.toEuclideanCLM_apply]

end WeakFocus

section WeakFocusLaws

open Dynamics.Degenerate

/-- The data of `weakFocusField` at its Hopf point, `H = ω₀²`. -/
@[tmio T, powerlib_foundation] private theorem weakFocus_data {lam g2 g3 ω₀ : ℝ}
    (hω : 0 < ω₀) (hl : 0 < lam) :
    IsCriticalPair (weakFocusField (ω₀ ^ 2) lam g2 g3) 0 ω₀ (weakFocusQ ω₀) (weakFocusP ω₀) ∧
      firstLyapunov (weakFocusField (ω₀ ^ 2) lam g2 g3) 0 ω₀ (weakFocusQ ω₀) (weakFocusP ω₀) =
        -hopfCoeff (ω₀ ^ 2) lam g2 g3 /
          (2 * lam * ω₀ ^ 3 * (lam ^ 2 + ω₀ ^ 2) ^ 2 * (lam ^ 2 + 4 * ω₀ ^ 2)) := by
  have hω0 : ω₀ ≠ 0 := hω.ne'
  have hl0 : lam ≠ 0 := hl.ne'
  have hS : ω₀ ^ 2 + lam ^ 2 ≠ 0 := by positivity
  have hS4 : lam ^ 2 + 4 * ω₀ ^ 2 ≠ 0 := by positivity
  have hJ := weakFocus_jacobianC (ω₀ ^ 2) lam g2 g3
  refine ⟨⟨?_, hω, ?_, ?_, ?_⟩, ?_⟩
  · apply Dynamics.state3_ext <;> simp [weakFocusField, weakFocusG]
  · rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, weakFocusQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals field_simp
  · rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, weakFocusP, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals field_simp
  · simp [dotProduct, Fin.sum_univ_three, weakFocusP, weakFocusQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (field_simp; ring)
  set r : Fin 3 → ℂ := ![((1 / ω₀ ^ 2 : ℝ) : ℂ), 0, ((1 / lam : ℝ) : ℂ)]
  set s : Fin 3 → ℂ := ![((1 / (3 * ω₀ ^ 2) : ℝ) : ℂ), ((2 / (3 * ω₀) : ℝ) : ℂ) * I,
    ((-lam / (lam ^ 2 + 4 * ω₀ ^ 2) : ℝ) : ℂ) +
      ((2 * ω₀ / (lam ^ 2 + 4 * ω₀ ^ 2) : ℝ) : ℂ) * I]
  have hdet : (jacobianC (weakFocusField (ω₀ ^ 2) lam g2 g3) 0).det =
      ((-(ω₀ ^ 2 * lam) : ℝ) : ℂ) := by
    rw [hJ, Matrix.det_fin_three]
    simp [Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  have hdet2 : (shift2 (jacobianC (weakFocusField (ω₀ ^ 2) lam g2 g3) 0) ω₀).det =
      ((-3 * ω₀ ^ 2 * lam : ℝ) : ℂ) + ((-6 * ω₀ ^ 3 : ℝ) : ℂ) * I := by
    rw [hJ, shift2, Matrix.det_fin_three]
    simp [Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; ring)
  have hr : jacobianC (weakFocusField (ω₀ ^ 2) lam g2 g3) 0 *ᵥ r =
      toC (Dynamics.mk3 0 (-1) (-1)) := by
    rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, r, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals field_simp
  have hs : shift2 (jacobianC (weakFocusField (ω₀ ^ 2) lam g2 g3) 0) ω₀ *ᵥ s =
      toC (Dynamics.mk3 0 (-1) (-1)) := by
    rw [hJ, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, s, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; ring)
  have hu1 := hdet ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hω0) hl0)))
  have hne : ((-3 * ω₀ ^ 2 * lam : ℝ) : ℂ) + ((-6 * ω₀ ^ 3 : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h'
    have : 0 < 3 * ω₀ ^ 2 * lam := by positivity
    linarith
  have hu2 := hdet2 ▸ isUnit_iff_ne_zero.mpr hne
  rw [weakFocusField_eq_ridge] at hu1 hu2 hr hs ⊢
  rw [firstLyapunov_ridge _ _ _ _ (contDiff_weakFocusG g2 g3) hu1 hu2 hr hs]
  obtain ⟨-, h2, h3⟩ := weakFocusG_derivs g2 g3 0
  simp only [map_zero, h2, h3, mul_zero, add_zero]
  simp [funC, pairing_apply, Fin.sum_univ_three, basisVec, weakFocusQ, weakFocusP, r, s,
    weakFocusXi, hopfCoeff, Complex.mul_re, Complex.mul_im, pow_two, -Complex.ofReal_mul,
    -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_sub,
    -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

@[tmio T, powerlib_foundation] private theorem weakFocus_spans {H lam g2 g3 ω₀ : ℝ}
    (hω : 0 < ω₀) (hl : 0 < lam) :
    (∀ v, jacobianC (weakFocusField H lam g2 g3) 0 *ᵥ v = ((ω₀ : ℂ) * I) • v →
      ∃ c : ℂ, v = c • weakFocusQ ω₀) ∧
    (∀ v, (jacobianC (weakFocusField H lam g2 g3) 0)ᵀ *ᵥ v = (-((ω₀ : ℂ) * I)) • v →
      ∃ c : ℂ, v = c • weakFocusP ω₀) := by
  have hJ := weakFocus_jacobianC H lam g2 g3
  have hω' : (ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have hne : ∀ σ : ℝ, (lam : ℂ) + σ * I ≠ 0 := by
    intro σ h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  constructor
  · intro v hv
    have h0 := congrFun hv 0
    have h2 := congrFun hv 2
    rw [hJ] at h0 h2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h2
    have hv2 : v 2 = 0 := by
      have : ((lam : ℂ) + ω₀ * I) * v 2 = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp this).resolve_left (hne ω₀)
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i
    · simp [weakFocusQ]
    · simp [weakFocusQ]; linear_combination h0
    · simp [weakFocusQ, hv2]
  · intro v hv
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    rw [hJ] at h1 h2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    have hv2 : v 2 = 0 := by
      rcases h2 with h2 | h2
      · exfalso
        have h' := congrArg Complex.re h2
        simp at h'
        linarith
      · exact h2
    refine ⟨((-2 * ω₀ : ℝ) : ℂ) * I * v 1, ?_⟩
    ext i; fin_cases i
    · simp [weakFocusP]; linear_combination h1
    · simp [weakFocusP]; field_simp; linear_combination v 1 * Complex.I_sq
    · simp [weakFocusP, hv2]

/-- The critical pair of the weak-focus normal form at `ω₀ = √H`. -/
@[tmio T, powerlib_foundation] theorem isCriticalPair_weakFocus {H lam g2 g3 : ℝ} (hH : 0 < H)
    (hl : 0 < lam) :
    IsCriticalPair (weakFocusField H lam g2 g3) 0 √H (weakFocusQ √H) (weakFocusP √H) := by
  have h := (weakFocus_data (g2 := g2) (g3 := g3) (Real.sqrt_pos.mpr hH) hl).1
  rwa [Real.sq_sqrt hH.le] at h

/-- **`ℓ₁` of the weak-focus normal form**:
`ℓ₁ = −κ/(2λω₀³(λ² + H)²(λ² + 4H))`, `κ = hopfCoeff H λ g₂ g₃`, `ω₀ = √H`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_weakFocus {H lam g2 g3 : ℝ} (hH : 0 < H)
    (hl : 0 < lam) :
    firstLyapunov (weakFocusField H lam g2 g3) 0 √H (weakFocusQ √H) (weakFocusP √H) =
      -hopfCoeff H lam g2 g3 / (2 * lam * √H ^ 3 * (lam ^ 2 + H) ^ 2 * (lam ^ 2 + 4 * H)) := by
  have h := (weakFocus_data (g2 := g2) (g3 := g3) (Real.sqrt_pos.mpr hH) hl).2
  rwa [Real.sq_sqrt hH.le] at h

/-- **Weak focus from `ℓ₁ < 0`.** A `C¹` field in the hypotheses of
`Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus` whose cubic normal form
`weakFocusField H λ g₂ g₃` has, for some critical pair at `ω₀ = √H`, a negative first Lyapunov
coefficient is locally asymptotically stable. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_weakFocus_firstLyapunov
    {f : State 3 → State 3} {T : State 3 →L[ℝ] State 3} {G : State 3 → ℝ} {H lam g2 g3 : ℝ}
    (hf : ContDiff ℝ 1 f) (hT : Function.Injective T) (hH : 0 < H) (hl : 0 < lam)
    (hf0 : ∀ z, T (f z) 0 = T z 1) (hf1 : ∀ z, T (f z) 1 = -H * T z 0 - G z)
    (hf2 : ∀ z, T (f z) 2 = -lam * T z 2 - G z)
    (hG : ∃ ρ > 0, ∃ C, ∀ z, |(lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)| ≤ ρ →
      |G z - (g2 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 2 +
        g3 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 3)| ≤
        C * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 4)
    {q p : Fin 3 → ℂ} (hc : IsCriticalPair (weakFocusField H lam g2 g3) 0 √H q p)
    (hl1 : firstLyapunov (weakFocusField H lam g2 g3) 0 √H q p < 0) :
    LocalAsymptoticStable f 0 := by
  have hω := Real.sqrt_pos.mpr hH
  obtain ⟨h1, h2⟩ := weakFocus_spans (H := H) (g2 := g2) (g3 := g3) hω hl
  have hs := sign_firstLyapunov_eq h1 h2 (isCriticalPair_weakFocus hH hl) hc
  rw [firstLyapunov_weakFocus hH hl, sign_neg hl1, eq_comm, sign_eq_neg_one_iff] at hs
  have hd : 0 < 2 * lam * √H ^ 3 * (lam ^ 2 + H) ^ 2 * (lam ^ 2 + 4 * H) := by positivity
  have hκ : 0 < hopfCoeff H lam g2 g3 := by
    rw [neg_div, neg_lt_zero, div_pos_iff_of_pos_right hd] at hs
    exact hs
  exact localAsymptoticStable_of_hopf_weakFocus hf hT hH hl hf0 hf1 hf2 hG hκ

end WeakFocusLaws

/-! ## Computing the forms from explicit first and second derivatives -/

/-- `B` from an explicit derivative `L₁` of `f` (everywhere) and of its column `y ↦ L₁ y e_j`. -/
@[tmio T, powerlib_foundation] theorem hess_eq_of_hasFDerivAt {f : State n → State n}
    {x₀ : State n} (hf : ContDiff ℝ 2 f) {L1 : State n → State n →L[ℝ] State n}
    (h1 : ∀ y, HasFDerivAt f (L1 y) y) {j : Fin n} {L2 : State n →L[ℝ] State n}
    (h2 : HasFDerivAt (fun y => L1 y (basisVec j)) L2 x₀) (k i : Fin n) :
    hess f x₀ k i j = L2 (basisVec i) k := by
  have hfd : fderiv ℝ f = L1 := funext fun y => (h1 y).fderiv
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x₀ :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x₀
  have e := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ => basisVec j) hd
    (differentiableAt_const _)
  have e2 : fderiv ℝ (fderiv ℝ f) x₀ (basisVec i) (basisVec j) =
      fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x₀ (basisVec i) := by
    rw [e]; simp
  rw [hess_eq, e2, hfd, h2.fderiv]

/-- `C` from explicit derivatives: `L₁` of `f`, `L₂ y` of the column `y ↦ L₁ y e_l` (everywhere)
and `L₃` of `y ↦ L₂ y e_j` at `x₀`. -/
@[tmio T, powerlib_foundation] theorem third_eq_of_hasFDerivAt {f : State n → State n}
    {x₀ : State n} (hf : ContDiff ℝ 3 f) {L1 : State n → State n →L[ℝ] State n}
    (h1 : ∀ y, HasFDerivAt f (L1 y) y) {l : Fin n} {L2 : State n → State n →L[ℝ] State n}
    (h2 : ∀ y, HasFDerivAt (fun y => L1 y (basisVec l)) (L2 y) y) {j : Fin n}
    {L3 : State n →L[ℝ] State n} (h3 : HasFDerivAt (fun y => L2 y (basisVec j)) L3 x₀)
    (k i : Fin n) : third f x₀ k i j l = L3 (basisVec i) k := by
  have hfd : fderiv ℝ f = L1 := funext fun y => (h1 y).fderiv
  have hF : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (m := 2) (by norm_num)
  have hd1 : ∀ y, DifferentiableAt ℝ (fderiv ℝ f) y := fun y =>
    hF.differentiable (by norm_num) y
  have hF2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hF.fderiv_right (m := 1) (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x₀ :=
    hF2.differentiable (by norm_num) x₀
  have row : ∀ y, fderiv ℝ (fderiv ℝ f) y (basisVec j) (basisVec l) = L2 y (basisVec j) := by
    intro y
    have e := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ => basisVec l) (hd1 y)
      (differentiableAt_const _)
    have e2 : fderiv ℝ (fderiv ℝ f) y (basisVec j) (basisVec l) =
        fderiv ℝ (fun y => fderiv ℝ f y (basisVec l)) y (basisVec j) := by
      rw [e]; simp
    rw [e2, hfd, (h2 y).fderiv]
  have hdj : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ f) y (basisVec j)) x₀ :=
    hd2.clm_apply (differentiableAt_const _)
  have e3 := fderiv_clm_apply (c := fderiv ℝ (fderiv ℝ f)) (u := fun _ => basisVec j) hd2
    (differentiableAt_const _)
  have e4 := fderiv_clm_apply (c := fun y => fderiv ℝ (fderiv ℝ f) y (basisVec j))
    (u := fun _ => basisVec l) hdj (differentiableAt_const _)
  have e5 : fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x₀ (basisVec i) (basisVec j) (basisVec l) =
      fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y (basisVec j) (basisVec l)) x₀ (basisVec i) := by
    rw [e4, e3]
    simp
  rw [third_eq, e5]
  simp only [row]
  rw [h3.fderiv]

/-! ## Products of a nonlinearity with a linear functional -/

/-- The field `x ↦ φ(ℓ x) m(x) v`. -/
def prodRidge (ℓ m : State n →L[ℝ] ℝ) (φ : ℝ → ℝ) (v : State n) (x : State n) : State n :=
  (φ (ℓ x) * m x) • v


section ProdRidge

variable (ℓ m : State n →L[ℝ] ℝ) (v : State n) {φ φ1 φ2 φ3 : ℝ → ℝ}

@[tmio T, powerlib_foundation] theorem contDiff_prodRidge (hφ : ContDiff ℝ 3 φ) :
    ContDiff ℝ 3 (prodRidge ℓ m φ v) :=
  ((hφ.comp ℓ.contDiff).mul m.contDiff).smul contDiff_const

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_prodRidge
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (y : State n) :
    HasFDerivAt (prodRidge ℓ m φ v)
      ((φ1 (ℓ y) * m y) • ℓ.smulRight v + φ (ℓ y) • m.smulRight v) y := by
  have h := (((h1 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).mul m.hasFDerivAt).smul_const v
  refine h.congr_fderiv ?_
  ext1 w
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply, smul_smul, ← add_smul]
  congr 1
  ring

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_prodRidge_col
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t) (w y : State n) :
    HasFDerivAt (fun y => ((φ1 (ℓ y) * m y) • ℓ.smulRight v + φ (ℓ y) • m.smulRight v) w)
      (((φ2 (ℓ y) * m y * ℓ w + φ1 (ℓ y) * m w) • ℓ + (φ1 (ℓ y) * ℓ w) • m).smulRight v) y := by
  have ha := ((h2 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).mul m.hasFDerivAt
  have hb := (h1 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt
  have h := ((ha.mul_const (ℓ w)).add (hb.mul_const (m w))).smul_const v
  have e : (fun y => ((φ1 (ℓ y) * m y) • ℓ.smulRight v + φ (ℓ y) • m.smulRight v) w) =
      fun y => (φ1 (ℓ y) * m y * ℓ w + φ (ℓ y) * m w) • v := by
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

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_prodRidge_col2
    (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t) (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t)
    (w u y : State n) :
    HasFDerivAt
      (fun y => (((φ2 (ℓ y) * m y * ℓ w + φ1 (ℓ y) * m w) • ℓ +
        (φ1 (ℓ y) * ℓ w) • m).smulRight v) u)
      (((φ3 (ℓ y) * m y * ℓ w * ℓ u + φ2 (ℓ y) * (m w * ℓ u + ℓ w * m u)) • ℓ +
        (φ2 (ℓ y) * ℓ w * ℓ u) • m).smulRight v) y := by
  have ha := (((h3 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).mul m.hasFDerivAt).mul_const
    (ℓ w * ℓ u)
  have hb := ((h2 (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).mul_const (m w * ℓ u + ℓ w * m u)
  have h := (ha.add hb).smul_const v
  have e : (fun y => (((φ2 (ℓ y) * m y * ℓ w + φ1 (ℓ y) * m w) • ℓ +
        (φ1 (ℓ y) * ℓ w) • m).smulRight v) u) =
      fun y => (φ2 (ℓ y) * m y * (ℓ w * ℓ u) + φ1 (ℓ y) * (m w * ℓ u + ℓ w * m u)) • v := by
    funext z
    simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul]
    congr 1
    ring
  rw [e]
  refine h.congr_fderiv ?_
  ext1 z'
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply]
  congr 1
  ring

/-- `B` of `φ(ℓ x) m(x) v`: `(φ''(ℓ x₀) ℓ(e_i) ℓ(e_j) m(x₀) + φ'(ℓ x₀)(ℓ(e_i) m(e_j) +
ℓ(e_j) m(e_i))) v`. -/
@[tmio T, powerlib_foundation] theorem hess_prodRidge (hφ : ContDiff ℝ 3 φ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t) (x₀ : State n)
    (k i j : Fin n) :
    hess (prodRidge ℓ m φ v) x₀ k i j =
      (φ2 (ℓ x₀) * ℓ (basisVec i) * ℓ (basisVec j) * m x₀ +
        φ1 (ℓ x₀) * (ℓ (basisVec i) * m (basisVec j) + ℓ (basisVec j) * m (basisVec i))) *
        v k := by
  rw [hess_eq_of_hasFDerivAt ((contDiff_prodRidge ℓ m v hφ).of_le (by norm_num))
    (hasFDerivAt_prodRidge ℓ m v h1) (hasFDerivAt_prodRidge_col ℓ m v h1 h2 _ x₀)]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, PiLp.smul_apply]
  ring

/-- `C` of `φ(ℓ x) m(x) v`. -/
@[tmio T, powerlib_foundation] theorem third_prodRidge (hφ : ContDiff ℝ 3 φ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t) (x₀ : State n) (k i j l : Fin n) :
    third (prodRidge ℓ m φ v) x₀ k i j l =
      (φ3 (ℓ x₀) * ℓ (basisVec i) * ℓ (basisVec j) * ℓ (basisVec l) * m x₀ +
        φ2 (ℓ x₀) * (ℓ (basisVec i) * ℓ (basisVec j) * m (basisVec l) +
          ℓ (basisVec i) * ℓ (basisVec l) * m (basisVec j) +
          ℓ (basisVec j) * ℓ (basisVec l) * m (basisVec i))) * v k := by
  rw [third_eq_of_hasFDerivAt (contDiff_prodRidge ℓ m v hφ) (hasFDerivAt_prodRidge ℓ m v h1)
    (hasFDerivAt_prodRidge_col ℓ m v h1 h2 _) (hasFDerivAt_prodRidge_col2 ℓ m v h2 h3 _ _ x₀)]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, PiLp.smul_apply]
  ring

@[tmio T, powerlib_foundation] private theorem funC_mul2 (a b : State n →L[ℝ] ℝ)
    (u w : Fin n → ℂ) :
    funC a u * funC b w = ∑ i, ∑ j, (a (basisVec i) : ℂ) * (b (basisVec j) : ℂ) * u i * w j := by
  simp only [funC, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[tmio T, powerlib_foundation] private theorem funC_mul3 (a b c : State n →L[ℝ] ℝ)
    (u w z : Fin n → ℂ) :
    funC a u * funC b w * funC c z = ∑ i, ∑ j, ∑ l, (a (basisVec i) : ℂ) *
      (b (basisVec j) : ℂ) * (c (basisVec l) : ℂ) * u i * w j * z l := by
  rw [funC_mul2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [funC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `B(u, w) = (φ''(ℓ x₀) m(x₀) ℓ(u) ℓ(w) + φ'(ℓ x₀)(ℓ(u) m(w) + m(u) ℓ(w))) v` for
`φ(ℓ x) m(x) v`. -/
@[tmio T, powerlib_foundation] theorem bilinC_prodRidge (hφ : ContDiff ℝ 3 φ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t) (x₀ : State n)
    (u w : Fin n → ℂ) :
    bilinC (prodRidge ℓ m φ v) x₀ u w =
      ((φ2 (ℓ x₀) : ℂ) * (m x₀ : ℂ) * (funC ℓ u * funC ℓ w) +
        (φ1 (ℓ x₀) : ℂ) * (funC ℓ u * funC m w + funC m u * funC ℓ w)) • toC v := by
  ext k
  rw [bilinC_apply, Pi.smul_apply, smul_eq_mul, funC_mul2, funC_mul2, funC_mul2]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, toC_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hess_prodRidge ℓ m v hφ h1 h2]
  push_cast
  ring

/-- `C(u, w, z) = (φ'''(ℓ x₀) m(x₀) ℓ(u) ℓ(w) ℓ(z) + φ''(ℓ x₀)(ℓ(u) ℓ(w) m(z) + ℓ(u) m(w) ℓ(z)
+ m(u) ℓ(w) ℓ(z))) v` for `φ(ℓ x) m(x) v`. -/
@[tmio T, powerlib_foundation] theorem trilinC_prodRidge (hφ : ContDiff ℝ 3 φ)
    (h1 : ∀ t, HasDerivAt φ (φ1 t) t) (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (h3 : ∀ t, HasDerivAt φ2 (φ3 t) t) (x₀ : State n) (u w z : Fin n → ℂ) :
    trilinC (prodRidge ℓ m φ v) x₀ u w z =
      ((φ3 (ℓ x₀) : ℂ) * (m x₀ : ℂ) * (funC ℓ u * funC ℓ w * funC ℓ z) +
        (φ2 (ℓ x₀) : ℂ) * (funC ℓ u * funC ℓ w * funC m z + funC ℓ u * funC m w * funC ℓ z +
          funC m u * funC ℓ w * funC ℓ z)) • toC v := by
  ext k
  rw [trilinC_apply, Pi.smul_apply, smul_eq_mul, funC_mul3, funC_mul3, funC_mul3, funC_mul3]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, toC_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [third_prodRidge ℓ m v hφ h1 h2 h3]
  push_cast
  ring

end ProdRidge

/-! ## Sums of fields -/

@[tmio T, powerlib_foundation] theorem hess_add {f g : State n → State n} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x₀ : State n) (k i j : Fin n) :
    hess (f + g) x₀ k i j = hess f x₀ k i j + hess g x₀ k i j := by
  simp only [hess, iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, _root_.add_apply,
    PiLp.add_apply]

@[tmio T, powerlib_foundation] theorem third_add {f g : State n → State n}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x₀ : State n) (k i j l : Fin n) :
    third (f + g) x₀ k i j l = third f x₀ k i j l + third g x₀ k i j l := by
  simp only [third, iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, _root_.add_apply,
    PiLp.add_apply]

@[tmio T, powerlib_foundation] theorem bilinC_add {f g : State n → State n}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x₀ : State n) (u w : Fin n → ℂ) :
    bilinC (f + g) x₀ u w = bilinC f x₀ u w + bilinC g x₀ u w := by
  ext k
  simp only [bilinC_apply, hess_add hf hg, Pi.add_apply, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib]

@[tmio T, powerlib_foundation] theorem trilinC_add {f g : State n → State n}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x₀ : State n) (u w z : Fin n → ℂ) :
    trilinC (f + g) x₀ u w z = trilinC f x₀ u w z + trilinC g x₀ u w z := by
  ext k
  simp only [trilinC_apply, third_add hf hg, Pi.add_apply, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib]

end powerlib.NormalForm.LyapunovCoefficient
