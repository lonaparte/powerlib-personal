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
import GFL.TheoremB
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace GFL

open Matrix

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

end GFL
