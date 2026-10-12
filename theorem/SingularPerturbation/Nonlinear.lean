import theorem.SingularPerturbation.Linear
import theorem.Flow.Linearization
import theorem.Dynamics.State

/-! # Nonlinear singularly perturbed systems: local exponential stability for small `ε`

Foundation layer (category B).

Sources: work-sync `theory/T-singular-perturbation.md` §1.3–§1.4 (reduced slow system on the
slow manifold, attractivity `Re λ(∂g/∂y) < 0`), `theory/T-tikhonov.md` §1.2 (linearized form of
the stability conditions), `theory/T-small-signal-stability.md` §1.4 (Schur complement).

System (continuous time, autonomous):
```
ẋ = f(x, z),      ε ż = g(x, z),      x ∈ ℝⁿ (slow), z ∈ ℝᵐ (fast),
```
written as one field `Φ = (f, g) : ℝⁿ⁺ᵐ → ℝⁿ⁺ᵐ` (`Dynamics.State (n + m)`, state order: the `n`
slow coordinates, then the `m` fast ones, via `finSumFinEquiv`), globally `C¹`, with an
equilibrium `w₀` (`Φ w₀ = 0`). The `ε`-system is `F_ε = D_ε Φ`, `D_ε = diag(Iₙ, ε⁻¹ Iₘ)`.
Let `J` be the block Jacobian of `Φ` at `w₀` (`A₁₁ = ∂f/∂x`, `A₁₂ = ∂f/∂z`, `A₂₁ = ∂g/∂x`,
`A₂₂ = ∂g/∂z`).

Result (`exists_epsStar_locallyExponentiallyStable`): if the boundary-layer Jacobian `A₂₂` is
Hurwitz and the reduced (Schur-complement) Jacobian `A₁₁ − A₁₂A₂₂⁻¹A₂₁` is Hurwitz, there is
`ε* > 0` such that for every `ε ∈ (0, ε*)` the full nonlinear system is locally exponentially
stable at `w₀`. Proof: the Jacobian of `F_ε` is `D_ε J = [[A₁₁, A₁₂], [A₂₁/ε, A₂₂/ε]]`
(`fderiv_scaledField`), which is Hurwitz for small `ε` by Kokotović's theorem
(`LinearSP.exists_epsStar_exponentiallyStable`), and the linearization theorem
(`Flow.locallyExponentiallyStable_of_isHurwitz_jacobian`) applies. With explicit Lyapunov
solutions `P₀`, `P₂`, `ε*` is the explicit `LinearSP.epsStar P₀ P₂`.

Model boundary: equilibrium-level (local) statement; `ε` fixed in `(0, ε*)`; no claim about
the size of the basin, its uniformity in `ε`, or finite-horizon `O(ε)` approximation.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix

variable {n m : ℕ}

/-- `diag(Iₙ, ε⁻¹ Iₘ)` in the `(x, z)` block order. -/
def scaleBlocks (n m : ℕ) (ε : ℝ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  fromBlocks 1 0 0 (ε⁻¹ • 1)

/-- `diag(Iₙ, ε⁻¹ Iₘ)` on `Fin (n + m)`. -/
def scaleMatrix (n m : ℕ) (ε : ℝ) : Matrix (Fin (n + m)) (Fin (n + m)) ℝ :=
  (scaleBlocks n m ε).reindex finSumFinEquiv finSumFinEquiv

/-- The `ε`-scaled field `F_ε(w) = D_ε Φ(w)` (`ẋ = f`, `ż = g/ε`). -/
def scaledField (ε : ℝ) (Φ : Dynamics.State (n + m) → Dynamics.State (n + m))
    (w : Dynamics.State (n + m)) : Dynamics.State (n + m) :=
  Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ) (scaleMatrix n m ε) (Φ w)

/-- The linear singularly perturbed system formed by the blocks of `J`. -/
def blocksSP (J : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) : LinearSP n m :=
  ⟨J.toBlocks₁₁, J.toBlocks₁₂, J.toBlocks₂₁, J.toBlocks₂₂⟩

@[powerlib_foundation] theorem scaleBlocks_mul (J : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ε : ℝ) : scaleBlocks n m ε * J = (blocksSP J).blockMatrix ε := by
  conv_lhs => rw [← fromBlocks_toBlocks J]
  rw [scaleBlocks, fromBlocks_multiply]
  simp [LinearSP.blockMatrix, blocksSP]

/-- Jacobian of the scaled field: `D_ε J`, i.e. the full matrix `[[A₁₁, A₁₂], [A₂₁/ε, A₂₂/ε]]`. -/
@[powerlib_foundation] theorem fderiv_scaledField {Φ : Dynamics.State (n + m) → Dynamics.State (n + m)}
    {w₀ : Dynamics.State (n + m)} (J : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (hd : DifferentiableAt ℝ Φ w₀)
    (hJ : fderiv ℝ Φ w₀ = Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ)
      (J.reindex finSumFinEquiv finSumFinEquiv)) (ε : ℝ) :
    fderiv ℝ (scaledField ε Φ) w₀ =
      Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ) ((blocksSP J).stateMatrix ε) := by
  have h := ((Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ)
    (scaleMatrix n m ε)).hasFDerivAt.comp w₀ hd.hasFDerivAt).fderiv
  have hcomp : (Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ) (scaleMatrix n m ε)).comp
      (fderiv ℝ Φ w₀) = Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ)
        ((blocksSP J).stateMatrix ε) := by
    rw [hJ, ← ContinuousLinearMap.mul_def, ← map_mul]
    congr 1
    simp only [scaleMatrix, LinearSP.stateMatrix, ← scaleBlocks_mul, reindex_apply,
      submatrix_mul_equiv]
  rw [← hcomp]
  exact h

@[powerlib_foundation] theorem scaledField_contDiff {Φ : Dynamics.State (n + m) → Dynamics.State (n + m)}
    (hΦ : ContDiff ℝ 1 Φ) (ε : ℝ) : ContDiff ℝ 1 (scaledField ε Φ) :=
  (Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ) (scaleMatrix n m ε)).contDiff.comp hΦ

/-- **Nonlinear two-time-scale stability**: `A₂₂` and the Schur complement Hurwitz ⇒ there is
`ε* > 0` such that `ẋ = f(x,z)`, `εż = g(x,z)` is locally exponentially stable at the
equilibrium for every `ε ∈ (0, ε*)`. -/
@[powerlib_foundation] theorem exists_epsStar_locallyExponentiallyStable
    {Φ : Dynamics.State (n + m) → Dynamics.State (n + m)} {w₀ : Dynamics.State (n + m)}
    (hΦ : ContDiff ℝ 1 Φ) (heq : Φ w₀ = 0) (J : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (hJ : fderiv ℝ Φ w₀ = Matrix.toEuclideanCLM (n := Fin (n + m)) (𝕜 := ℝ)
      (J.reindex finSumFinEquiv finSumFinEquiv))
    (hA22 : LinearSystems.IsHurwitz J.toBlocks₂₂)
    (hA0 : LinearSystems.IsHurwitz (J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁)) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      LocallyExponentiallyStable (scaledField ε Φ) w₀ := by
  obtain ⟨εs, hεs, h⟩ := (blocksSP J).exists_epsStar_exponentiallyStable hA22 hA0
  refine ⟨εs, hεs, fun ε hε hlt => ?_⟩
  have hH := (h ε hε hlt).1
  refine Flow.locallyExponentiallyStable_of_isHurwitz_jacobian _ (scaledField_contDiff hΦ ε)
    ?_ (fderiv_scaledField J (hΦ.differentiable one_ne_zero w₀) hJ ε) hH
  simp [scaledField, heq]

end powerlib.SingularPerturbation
