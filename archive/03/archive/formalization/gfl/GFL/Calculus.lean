/-
  Calculus completions (require Mathlib's analysis tower).

  These upgrade the two facts that Theorem B's `schur_term_zero` took as hypotheses —
  the IFT linearisation `A·v = −c` and the vanishing `i_d`-tangent `v₀ = 0` (Cor 0a) —
  from documented hypotheses to *proved* statements, using real derivatives:

    * `syncCoeff_deriv_zero`    : Cor 0a as a literal derivative, `deriv(P_meas∘z*) = 0`.
    * `branch_iD_tangent_zero`  : `v₀ = 0` (the tangent of the constant `i_d`-component).
    * `branch_linearization`    : `A·v = −c` from differentiating `F_inner(z*(d),d) = 0`
                                  (the standard implicit-function-theorem linearisation).
    * `schur_term_zero_of_branch` : combines them — `ρᵀ A⁻¹ c = 0` follows from the
                                  differentiable (C¹) branch structure W3 alone.
-/
import GFL.TheoremA
import GFL.TheoremB
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

namespace GFL

open Matrix Filter
open scoped Topology

/-- **Corollary 0a as a literal derivative.**  The synchronising coefficient
`K := d/dd[P_meas(z*(d))]` is exactly `0`, because that map is the constant function
`P_ref` (`syncCoeff_zero`). -/
theorem syncCoeff_deriv_zero (p : Params) (S : InnerField p) (B : EquilibriumBranch p S)
    (d : ℝ) : deriv (fun d => Pmeas p (B.z d)) d = 0 := by
  have h : (fun d => Pmeas p (B.z d)) = fun _ => p.P_ref := funext (syncCoeff_zero p S B).2
  rw [h]; exact deriv_const d p.P_ref

/-- **The `i_d`-tangent vanishes (Cor 0a, derivative form).**  If the branch `z* : ℝ →
(Fin 8 → ℝ)` is differentiable with derivative `v` at `d₀` and its `i_d`-component
(coordinate `0`) is constant, then `v₀ = 0`. -/
theorem branch_iD_tangent_zero (z : ℝ → (Fin 8 → ℝ)) (v : Fin 8 → ℝ) (d₀ : ℝ)
    (hz : HasDerivAt z v d₀) (hconst : ∀ d, z d 0 = z d₀ 0) : v 0 = 0 := by
  -- the `i_d`-component (coordinate 0) of the branch
  have h0 : HasDerivAt (fun d => z d 0) (v 0) d₀ := (hasDerivAt_pi.mp hz) 0
  have hc : HasDerivAt (fun d => z d 0) 0 d₀ := by
    have he : (fun d => z d 0) = fun _ => z d₀ 0 := funext hconst
    rw [he]; exact hasDerivAt_const d₀ _
  exact h0.unique hc

/-- **Implicit-function-theorem linearisation (W3 differentiated).**
Let `z* : ℝ → (Fin 8 → ℝ)` be the branch with `HasDerivAt z* v d₀`, and let the inner
field `Φ : (Fin 8 → ℝ) → ℝ → (Fin 8 → ℝ)` be (jointly) differentiable at `(z* d₀, d₀)`
with derivative the Jacobian `L = [∂Φ/∂z | ∂Φ/∂dw] = [A | c]` (so `L (w, t) = A·w + t·c`,
in particular `L (v, 1) = A·v + c`).  If the branch consists of equilibria
(`Φ (z* d) d = 0` for all `d`), then differentiating gives

    `A · v + c = 0`,  i.e.  `A · v = −c`. -/
theorem branch_linearization
    {Φ : (Fin 8 → ℝ) → ℝ → (Fin 8 → ℝ)}
    (z : ℝ → (Fin 8 → ℝ)) (v : Fin 8 → ℝ) (d₀ : ℝ)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (c : Fin 8 → ℝ)
    (L : ((Fin 8 → ℝ) × ℝ) →L[ℝ] (Fin 8 → ℝ))
    (hz : HasDerivAt z v d₀)
    (hΦ : HasFDerivAt (fun q : (Fin 8 → ℝ) × ℝ => Φ q.1 q.2) L (z d₀, d₀))
    (hL : L (v, 1) = A *ᵥ v + c)
    (hbranch : ∀ d, Φ (z d) d = 0) :
    A *ᵥ v = -c := by
  -- bind the curve d ↦ (z* d, d) as a local constant so the chain rule infers it as the
  -- inner map (avoids higher-order unification picking the wrong inner function)
  set γ : ℝ → (Fin 8 → ℝ) × ℝ := fun d => (z d, d) with hγ_def
  have hγ : HasDerivAt γ (v, 1) d₀ := hz.prodMk (hasDerivAt_id d₀)
  have hΦ' : HasFDerivAt (fun q : (Fin 8 → ℝ) × ℝ => Φ q.1 q.2) L (γ d₀) := hΦ
  -- chain rule: d ↦ Φ(z* d, d) has derivative L (v, 1)
  have hcomp : HasDerivAt (fun d => Φ (z d) d) (L (v, 1)) d₀ := hΦ'.comp_hasDerivAt d₀ hγ
  -- but that composite is identically 0
  have hconst : HasDerivAt (fun d => Φ (z d) d) 0 d₀ := by
    have he : (fun d => Φ (z d) d) = fun _ => (0 : Fin 8 → ℝ) := funext hbranch
    rw [he]; exact hasDerivAt_const d₀ _
  have hzero : L (v, 1) = 0 := hcomp.unique hconst
  rw [hL] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- **Theorem B Schur term, fully derived from the C¹ branch (W3).**
Combining the IFT linearisation and the vanishing `i_d`-tangent, the O(1) Schur term
`ρᵀ A⁻¹ c = 0` follows from the differentiable branch structure alone (no `A·v = −c` or
`v₀ = 0` left as hypotheses). -/
theorem schur_term_zero_of_branch (p : Params)
    {Φ : (Fin 8 → ℝ) → ℝ → (Fin 8 → ℝ)}
    (z : ℝ → (Fin 8 → ℝ)) (v : Fin 8 → ℝ) (d₀ : ℝ)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det) (c : Fin 8 → ℝ)
    (L : ((Fin 8 → ℝ) × ℝ) →L[ℝ] (Fin 8 → ℝ))
    (hz : HasDerivAt z v d₀)
    (hΦ : HasFDerivAt (fun q : (Fin 8 → ℝ) × ℝ => Φ q.1 q.2) L (z d₀, d₀))
    (hL : L (v, 1) = A *ᵥ v + c)
    (hbranch : ∀ d, Φ (z d) d = 0)
    (hconst : ∀ d, z d 0 = z d₀ 0)
    (ρ : Fin 8 → ℝ) (hρ : ρ = (-(3 / 2) * p.kappa * p.Vg) • Pi.single 0 1) :
    ρ ⬝ᵥ (A⁻¹ *ᵥ c) = 0 :=
  schur_term_zero p A hA c v
    (branch_linearization z v d₀ A c L hz hΦ hL hbranch)
    (branch_iD_tangent_zero z v d₀ hz hconst) ρ hρ

/-! ### W3 from W2: the equilibrium branch is produced by the implicit function theorem

The inner field is written here in `(d, z)` order, `F : ℝ → (Fin 8 → ℝ) → (Fin 8 → ℝ)`,
`F d z`.  Given that `F` has continuous partial derivatives near the equilibrium `(d₀, z₀)`
(`F C¹`), with the partial in `z` (the inner Jacobian `f₂ d₀ z₀ = A`) **invertible** (W2),
Mathlib's implicit function theorem produces the C¹ branch — so W3 is *derived*, not assumed. -/

/-- **W3 via the implicit function theorem (existence + C¹ branch + linearisation).**
If `F` is `C¹` near `(d₀, z₀)` (continuous partials `f₁ = ∂F/∂d`, `f₂ = ∂F/∂z`), the inner
Jacobian `f₂ d₀ z₀` is invertible (W2), and `(d₀, z₀)` is an equilibrium (`F d₀ z₀ = 0`),
then there is a branch `z*` with `F d (z* d) = 0` near `d₀`, `z* d₀ = z₀`, and `z*` is
differentiable at `d₀` with tangent `v` satisfying `(f₂ d₀ z₀) v = −(f₁ d₀ z₀ 1)`
(the IFT linearisation `A·v = −c`). -/
theorem branch_of_ift
    {F : ℝ → (Fin 8 → ℝ) → (Fin 8 → ℝ)}
    {f₁ : ℝ → (Fin 8 → ℝ) → (ℝ →L[ℝ] (Fin 8 → ℝ))}
    {f₂ : ℝ → (Fin 8 → ℝ) → ((Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ))}
    {d₀ : ℝ} {z₀ : Fin 8 → ℝ}
    (df₁ : ∀ᶠ v in 𝓝 (d₀, z₀), HasFDerivAt (F · v.2) (f₁ v.1 v.2) v.1)
    (df₂ : ∀ᶠ v in 𝓝 (d₀, z₀), HasFDerivAt (F v.1 ·) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (↿f₁) (d₀, z₀)) (cf₂ : ContinuousAt (↿f₂) (d₀, z₀))
    (if₂ : (f₂ d₀ z₀).IsInvertible) (heq : F d₀ z₀ = 0) :
    ∃ z : ℝ → (Fin 8 → ℝ),
      (∀ᶠ d in 𝓝 d₀, F d (z d) = 0) ∧ z d₀ = z₀ ∧
      ∃ v : Fin 8 → ℝ, HasDerivAt z v d₀ ∧ (f₂ d₀ z₀) v = -(f₁ d₀ z₀ 1) := by
  refine ⟨implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂, ?_, ?_, ?_⟩
  · -- branch: F d (z* d) = 0 near d₀
    have h := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
    simpa [heq] using h
  · -- z* d₀ = z₀
    have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).self_of_nhds
    simpa using h.mp rfl
  · -- tangent v with (f₂ d₀ z₀) v = -(f₁ d₀ z₀ 1)
    refine ⟨(-(f₂ d₀ z₀).inverse ∘L f₁ d₀ z₀) 1, ?_, ?_⟩
    · exact (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).hasFDerivAt.hasDerivAt
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg]
      rw [if₂.self_apply_inverse]

/-- **Theorem B, unconditional modulo `F`'s smoothness.**  Specialising `branch_of_ift` to
the case where the inner Jacobian acts as the matrix `A` (`f₂ d₀ z₀ w = A·w`) and the
`dw`-partial direction is `c` (`f₁ d₀ z₀ 1 = c`): the IFT yields a C¹ branch whose tangent
`v` satisfies `A·v = −c` — exactly the hypothesis that `branch_linearization`/`schur_term_zero`
previously assumed.  Thus W3 (and `A·v = −c`) follow from W2 + smoothness. -/
theorem branch_linearization_of_ift
    {F : ℝ → (Fin 8 → ℝ) → (Fin 8 → ℝ)}
    {f₁ : ℝ → (Fin 8 → ℝ) → (ℝ →L[ℝ] (Fin 8 → ℝ))}
    {f₂ : ℝ → (Fin 8 → ℝ) → ((Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ))}
    {d₀ : ℝ} {z₀ : Fin 8 → ℝ} {A : Matrix (Fin 8) (Fin 8) ℝ} {c : Fin 8 → ℝ}
    (df₁ : ∀ᶠ v in 𝓝 (d₀, z₀), HasFDerivAt (F · v.2) (f₁ v.1 v.2) v.1)
    (df₂ : ∀ᶠ v in 𝓝 (d₀, z₀), HasFDerivAt (F v.1 ·) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (↿f₁) (d₀, z₀)) (cf₂ : ContinuousAt (↿f₂) (d₀, z₀))
    (if₂ : (f₂ d₀ z₀).IsInvertible) (heq : F d₀ z₀ = 0)
    (hf₂ : ∀ w, (f₂ d₀ z₀) w = A *ᵥ w) (hf₁ : f₁ d₀ z₀ 1 = c) :
    ∃ z : ℝ → (Fin 8 → ℝ),
      (∀ᶠ d in 𝓝 d₀, F d (z d) = 0) ∧ z d₀ = z₀ ∧
      ∃ v : Fin 8 → ℝ, HasDerivAt z v d₀ ∧ A *ᵥ v = -c := by
  obtain ⟨z, hz0, hzd, v, hv, hAv⟩ := branch_of_ift df₁ df₂ cf₁ cf₂ if₂ heq
  exact ⟨z, hz0, hzd, v, hv, by rw [← hf₂, hAv, hf₁]⟩

/-! ### Theorem A's `hbot` is a derived fact, not an axiom (A3)

Variant U sets the swing component `F9_U := 0` (§6).  So the Variant-U field is the inner field
with a constant `0` appended as the 9th component, and the 9th *row* of its Jacobian — the
gradient of that 9th component — is identically zero.  That is exactly the hypothesis `hbot`
of `variantU_zero_eigenvalue`: it is forced by the §6 model structure, not assumed. -/

/-- The Variant-U field: the inner field `F` with the swing component `F9_U ≡ 0` appended. -/
def variantUField (F : (Fin 9 → ℝ) → (Fin 8 → ℝ)) (y : Fin 9 → ℝ) : Fin 9 → ℝ :=
  Fin.snoc (F y) 0

/-- The 9th (swing) component of the Variant-U field is the constant `0`. -/
theorem variantUField_last (F : (Fin 9 → ℝ) → (Fin 8 → ℝ)) (y : Fin 9 → ℝ) :
    variantUField F y (Fin.last 8) = 0 := by
  simp only [variantUField, Fin.snoc_last]

/-- **`hbot` derived (A3).**  The Jacobian row of the swing component `F9_U` is identically zero:
`∂/∂y [ (variantUField F y) (last) ] = 0`, because that component is the constant `0`.  Hence the
last row of the Variant-U Jacobian vanishes — precisely the hypothesis `hbot` that Theorem A
takes.  (`variantU_zero_eigenvalue` then applies with `hbot j` obtained from this zero gradient.) -/
theorem variantU_lastrow_fderiv_zero (F : (Fin 9 → ℝ) → (Fin 8 → ℝ)) (y₀ : Fin 9 → ℝ) :
    HasFDerivAt (fun y => variantUField F y (Fin.last 8)) (0 : (Fin 9 → ℝ) →L[ℝ] ℝ) y₀ := by
  have he : (fun y => variantUField F y (Fin.last 8)) = fun _ => (0 : ℝ) :=
    funext (variantUField_last F)
  rw [he]; exact hasFDerivAt_const 0 y₀

/-- The Jacobian matrix of a vector field `G : (Fin 9 → ℝ) → (Fin 9 → ℝ)` at `y₀`:
entry `(i,j)` is the partial derivative `∂Gᵢ/∂yⱼ` (`= fderiv` of the `i`-th component applied to
the `j`-th coordinate direction). -/
noncomputable def jacobianMatrix (G : (Fin 9 → ℝ) → (Fin 9 → ℝ)) (y₀ : Fin 9 → ℝ) :
    Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => fderiv ℝ (fun y => G y i) y₀ (Pi.single j 1)

/-- **A3 end-to-end.**  Every entry of the last row of the *concrete* Variant-U Jacobian is `0`:
the swing component `F9_U ≡ 0` has zero gradient, so `∂(F9_U)/∂yⱼ = 0`. -/
theorem variantU_jacobian_lastrow_zero (F : (Fin 9 → ℝ) → (Fin 8 → ℝ)) (y₀ : Fin 9 → ℝ)
    (j : Fin 9) : jacobianMatrix (variantUField F) y₀ 8 j = 0 := by
  have hconst : (fun y => variantUField F y (8 : Fin 9)) = fun _ => (0 : ℝ) := by
    funext y
    have h8 : (8 : Fin 9) = Fin.last 8 := rfl
    rw [h8]; exact variantUField_last F y
  show fderiv ℝ (fun y => variantUField F y (8 : Fin 9)) y₀ (Pi.single j 1) = 0
  rw [hconst]; simp

/-- **A3 end-to-end — `hbot` discharged on the concrete Jacobian.**  `variantU_zero_eigenvalue`
applies directly to the actual Variant-U Jacobian matrix: `0 ∈ spec`, `det = 0`, with `e₉` a
nonzero left eigenvector.  `hbot` is no longer an input — it is produced by
`variantU_jacobian_lastrow_zero`. -/
theorem variantU_jacobian_zero_eigenvalue (F : (Fin 9 → ℝ) → (Fin 8 → ℝ)) (y₀ : Fin 9 → ℝ) :
    (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) ᵥ* jacobianMatrix (variantUField F) y₀ = 0 ∧
    (jacobianMatrix (variantUField F) y₀).det = 0 ∧
    (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) ≠ 0 :=
  variantU_zero_eigenvalue _ (variantU_jacobian_lastrow_zero F y₀)

end GFL
