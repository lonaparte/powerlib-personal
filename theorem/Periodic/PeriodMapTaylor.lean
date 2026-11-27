import theorem.Periodic.FlowDerivative
import theorem.Periodic.ForcedRegime

/-! # The cubic Taylor expansion of the flow and of the period map

Along a solution `x_*` of `ẋ = G(t, x)` let the field have the Taylor expansion
`G(r, x_* + u) = G(r, x_*) + A(r) u + Q₂(r)(u, u) + Q₃(r)(u, u, u) + O(‖u‖⁴)`. Then the solution
from `x_*(s) + e` is `x(t) = x_*(t) + y₁(t) + y₂(t) + y₃(t) + O(‖e‖⁴)`, where `y₁, y₂, y₃` solve the
first, second and third variational equations

* `ẏ₁ = A y₁`, `y₁(s) = e` (`y₁(t) = Φ(t, s) e`),
* `ẏ₂ = A y₂ + Q₂(y₁, y₁)`, `y₂(s) = 0`,
* `ẏ₃ = A y₃ + Q₂(y₁, y₂) + Q₂(y₂, y₁) + Q₃(y₁, y₁, y₁)`, `y₃(s) = 0`;

for `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` (symmetric) these are `ẏ₂ = A y₂ + ½ D²G[y₁, y₁]` and
`ẏ₃ = A y₃ + D²G[y₁, y₂] + ⅙ D³G[y₁, y₁, y₁]`. By variation of constants `y₂(t) = P₂(t)(e, e)`
and `y₃(t) = P₃(t)(e, e, e)` with the bilinear and trilinear maps
`P₂(t)(e, f) = ∫ₛᵗ Φ(t, r) Q₂(r)(Φ(r, s) e, Φ(r, s) f) dr` and
`P₃(t)(m) = ∫ₛᵗ Φ(t, r) [Q₂(r)(Φ(r, s) m₀, P₂(r)(m₁, m₂)) + Q₂(r)(P₂(r)(m₀, m₁), Φ(r, s) m₂) +
Q₃(r)(Φ(r, s) m₀, Φ(r, s) m₁, Φ(r, s) m₂)] dr`. At `s = 0`, `t = T` and a `T`-periodic `x_*` this is
the expansion `P(p + e) = p + M e + P₂(e, e) + P₃(e, e, e) + O(‖e‖⁴)` of the period map that
`theorem/Periodic/FlipReduction.lean` takes as its hypothesis `hTay`, with `M = Φ(T, 0)`.

The proof is three Grönwall steps (`FlowDerivative.norm_le_of_hasDerivWithinAt`) for the
remainders `a = u − y₁`, `b = a − y₂`, `z = b − y₃` of the deviation `u = x − x_*`: each solves
`ẇ = A w + (source)`, and the source is bounded by the previous step,
`Q₂(u, u) + Q₃(u, u, u) + R = O(‖e‖²)`, `Q₂(a, u) + Q₂(y₁, a) + Q₃(u, u, u) + R = O(‖e‖³)`,
`Q₂(y₁, b) + Q₂(b, y₁) + Q₂(a, a) + Q₃(u, u, u) − Q₃(y₁, y₁, y₁) + R = O(‖e‖⁴)`.

Scope.
* `ℝ^X` (`X → ℝ`, finite `X`, sup norm), continuous time, solutions on segments `[s, t]`, as in
  `theorem/Periodic/FlowDerivative.lean`; `G(r, ·)` is `K`-Lipschitz (existence of the flow and
  the a priori bound `‖x(r) − x_*(r)‖ ≤ e^{K(r − s)} ‖e‖`).
* The regularity of `G` enters as the Taylor expansion along `x_*` on `[s, t]`: continuous
  coefficient fields `A` (matrices), `Q₂` (continuous bilinear maps) and `Q₃` (continuous
  trilinear maps, `ContinuousMultilinearMap` on `Fin 3`) with `‖A(r) v‖ ≤ K ‖v‖`, `‖Q₂(r)‖ ≤ B₂`,
  `‖Q₃(r)‖ ≤ B₃` and the remainder `c₄ ‖u‖⁴` for `‖u‖ ≤ ρ`. For `G(r, ·)` of class `C⁴` with
  continuous `D_x²G`, `D_x³G` and `‖D_x⁴G‖ ≤ 24 c₄` near `x_*` it holds with `A = D_xG`,
  `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` (Taylor's theorem, Mathlib
  `map_add_eq_sum_add_integral_iteratedFDeriv`); that derivation from iterated derivatives is not
  carried out here. `Q₂`, `Q₃` need not be symmetric.
* `P₂ = secondVariation` and `P₃ = thirdVariation` are defined by their values on (pairs, triples
  of) basis vectors (`bilinOfBasis`, `multilinOfBasis`); `secondVariation_apply`,
  `thirdVariation_apply` identify them with the solutions of the forced variational equations
  for all arguments, through the linearity of the forced response in its input (`resp_add`,
  `resp_smul`, by uniqueness of solutions).
* The remainder constant is explicit (`taylorConst`), valid for `‖e‖ ≤ 1` with
  `e^{K(t − s)} ‖e‖ ≤ ρ`.
* Generic mathematics; no model family.

Source: Hartman, *Ordinary Differential Equations*, Ch. V (higher differentiability with respect
to initial conditions; the higher variational equations); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §5.4 (the Taylor coefficients of a Poincaré map, entering the
normal-form coefficients); the open item of `theorem/Periodic/FlipReduction.lean` (Scope: the
cubic Taylor expansion of the period map was a hypothesis there).

Results.
* `resp`, `resp_eq_integral`, `resp_start`, `hasDerivAt_resp`, `resp_add`, `resp_smul`,
  `norm_resp_le` — the response `y(t) = ∫ₛᵗ Φ(t, r) u(r) dr` of `ẏ = A y + u`, `y(s) = 0`.
* `bilinOfBasis`, `bilinOfBasis_apply`, `bilinOfBasis_eq`, `multilinOfBasis`,
  `multilinOfBasis_apply`, `multilinOfBasis_eq` — (multi)linear maps on `ℝ^X` from their values
  on basis vectors.
* `continuous_transition_mulVec`, `secondSource`, `continuous_secondSource`, `secondVariation`,
  `secondVariation_apply`, `hasDerivAt_secondVariation`, `secondVariation_eq_integral` — the
  second variation `P₂(t)`.
* `thirdSource`, `continuous_thirdSource`, `thirdSource_update_add`, `thirdSource_update_smul`,
  `thirdVariation`, `thirdVariation_apply`, `hasDerivAt_thirdVariation`,
  `thirdVariation_eq_integral` — the third variation `P₃(t)`.
* `taylorConst`, `norm_sub_taylor_le` — the cubic expansion of the flow,
  `‖x(t) − x_*(t) − Φ(t, s) e − P₂(t)(e, e) − P₃(t)(e, e, e)‖ ≤ C₄ ‖e‖⁴`.
* `periodMap_taylor` — the same for the period map at a `T`-periodic solution:
  `‖P(p + e) − p − M e − P₂(e, e) − P₃(e, e, e)‖ ≤ C₄ ‖e‖⁴` for `‖e‖ ≤ min 1 (ρ e^{−KT})`.

Corrections.
None: an extension (the cubic Taylor expansion of the period map, a hypothesis of
`theorem/Periodic/FlipReduction.lean`, derived from the field).

Family and connection conclusions.
None: static evidence on nonautonomous ODEs (the Taylor expansion of the flow).
-/

noncomputable section
namespace powerlib.Periodic.PeriodMapTaylor

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative (norm_le_of_hasDerivWithinAt hasDerivAt_transition_mulVec)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The response of the forced variational equation -/

/-- The response of `ẏ = A(t) y + u(t)` with `y(s) = 0`: LeanForControl's forced response with
input matrix `I`, `y(t) = ∫ₛᵗ Φ(t, r) u(r) dr` (`resp_eq_integral`). -/
def resp (A : ℝ → Matrix X X ℝ) (u : ℝ → X → ℝ) (s : ℝ) : ℝ → X → ℝ :=
  LinearSystems.forcedResponse A (fun _ => (1 : Matrix X X ℝ)) u s 0

variable {A : ℝ → Matrix X X ℝ}

@[tmio T, powerlib_foundation] theorem resp_eq_integral (u : ℝ → X → ℝ) (s t : ℝ) :
    resp A u s t = ∫ r in s..t, transition A t r *ᵥ u r := by
  simp [resp, LinearSystems.forcedResponse]

@[tmio T, powerlib_foundation] theorem resp_start (u : ℝ → X → ℝ) (s : ℝ) : resp A u s s = 0 :=
  LinearSystems.variationOfConstants_self s 0

@[tmio T, powerlib_foundation] theorem hasDerivAt_resp (hA : Continuous A) {u : ℝ → X → ℝ}
    (hu : Continuous u) (s r : ℝ) :
    HasDerivAt (resp A u s) (A r *ᵥ resp A u s r + u r) r :=
  hasDerivAt_forcedResponse hA hu s 0 r

@[tmio T, powerlib_foundation] theorem resp_add (hA : Continuous A) {u₁ u₂ : ℝ → X → ℝ}
    (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (s : ℝ) :
    resp A (fun r => u₁ r + u₂ r) s = fun r => resp A u₁ s r + resp A u₂ s r := by
  refine forced_eq_of_eq hA (hu₁.add hu₂) (hasDerivAt_resp hA (hu₁.add hu₂) s)
    (fun r => ?_) (t₀ := s) (by simp [resp_start])
  convert (hasDerivAt_resp hA hu₁ s r).add (hasDerivAt_resp hA hu₂ s r) using 1
  rw [Matrix.mulVec_add, Pi.add_apply]
  abel

@[tmio T, powerlib_foundation] theorem resp_smul (hA : Continuous A) {u : ℝ → X → ℝ}
    (hu : Continuous u) (c : ℝ) (s : ℝ) :
    resp A (fun r => c • u r) s = fun r => c • resp A u s r := by
  have hcu : Continuous fun r => c • u r := hu.const_smul c
  have h1 : ∀ r, HasDerivAt (resp A (fun r => c • u r) s)
      (A r *ᵥ resp A (fun r => c • u r) s r + c • u r) r := hasDerivAt_resp hA hcu s
  have h2 : ∀ r, HasDerivAt (fun r => c • resp A u s r)
      (A r *ᵥ (c • resp A u s r) + c • u r) r := fun r => by
    have := (hasDerivAt_resp hA hu s r).const_smul c
    rwa [smul_add, ← Matrix.mulVec_smul] at this
  exact forced_eq_of_eq (f := fun r => c • u r) hA hcu h1 h2 (t₀ := s)
    (by simp [resp_start])

/-- Grönwall for the response: `‖A(r) v‖ ≤ K ‖v‖` and `‖u‖ ≤ ε` on `[s, t]` give
`‖y(r)‖ ≤ ε (t − s) e^{K(t − s)}` on `[s, t]`. -/
@[tmio T, powerlib_foundation] theorem norm_resp_le (hA : Continuous A) {u : ℝ → X → ℝ}
    (hu : Continuous u) {s t K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hAK : ∀ r ∈ Icc s t, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖) (hub : ∀ r ∈ Icc s t, ‖u r‖ ≤ ε) :
    ∀ r ∈ Icc s t, ‖resp A u s r‖ ≤ ε * (t - s) * Real.exp (K * (t - s)) := by
  intro r hr
  have h := norm_le_of_hasDerivWithinAt hK hε
    (fun q _ => (hasDerivAt_resp hA hu s q).hasDerivWithinAt)
    (fun q hq => (norm_add_le _ _).trans (add_le_add (hAK q (Ico_subset_Icc_self hq) _)
      (hub q (Ico_subset_Icc_self hq))))
    (by rw [resp_start, norm_zero]) r hr
  simpa using h

/-! ## Multilinear maps on `ℝ^X` from their values on basis vectors -/

/-- The bilinear map on `ℝ^X` with the values `c i j` on pairs of standard basis vectors. -/
def bilinOfBasis (c : X → X → X → ℝ) : (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ :=
  ∑ i, ∑ j, (ContinuousLinearMap.proj i : (X → ℝ) →L[ℝ] ℝ).smulRight
    ((ContinuousLinearMap.proj j : (X → ℝ) →L[ℝ] ℝ).smulRight (c i j))

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem bilinOfBasis_apply (c : X → X → X → ℝ) (e f : X → ℝ) :
    bilinOfBasis c e f = ∑ i, ∑ j, (e i * f j) • c i j := by
  simp [bilinOfBasis, _root_.sum_apply, smul_smul]

/-- A bilinear map is the interpolation of its values on pairs of basis vectors. -/
@[tmio T, powerlib_foundation] theorem bilinOfBasis_eq (B : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] X → ℝ)
    (e f : X → ℝ) :
    bilinOfBasis (fun i j => B (Pi.single i 1) (Pi.single j 1)) e f = B e f := by
  have hsum : ∀ g : X → ℝ, g = ∑ i, g i • (Pi.single i 1 : X → ℝ) := fun g => by
    conv_lhs => rw [← Finset.univ_sum_single g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [bilinOfBasis_apply]
  conv_rhs => rw [hsum e, hsum f]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- The multilinear map on `(ℝ^X)^ι` with the values `c f` on tuples of standard basis vectors
`(e_{f l})_l`. -/
def multilinOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (ι → X) → X → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : ι => X → ℝ) (X → ℝ) :=
  ∑ f : ι → X, (ContinuousMultilinearMap.mkPiRing ℝ ι (c f)).compContinuousLinearMap
    fun l => (ContinuousLinearMap.proj (f l) : (X → ℝ) →L[ℝ] ℝ)

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem multilinOfBasis_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (c : (ι → X) → X → ℝ) (m : ι → X → ℝ) :
    multilinOfBasis c m = ∑ f : ι → X, (∏ l, m l (f l)) • c f := by
  simp [multilinOfBasis, _root_.sum_apply]

/-- A multilinear map is the interpolation of its values on tuples of basis vectors. -/
@[tmio T, powerlib_foundation] theorem multilinOfBasis_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MultilinearMap ℝ (fun _ : ι => X → ℝ) (X → ℝ)) (m : ι → X → ℝ) :
    multilinOfBasis (fun f => M fun l => Pi.single (f l) 1) m = M m := by
  rw [multilinOfBasis_apply]
  have hm : m = fun l => ∑ j, m l j • (Pi.single j 1 : X → ℝ) := by
    funext l
    conv_lhs => rw [← Finset.univ_sum_single (m l)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  conv_rhs => rw [hm, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ]

/-! ## The second and third variations -/

variable {Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ}
  {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ)}

@[tmio T, powerlib_foundation] theorem continuous_transition_mulVec (hA : Continuous A) (s : ℝ)
    (v : X → ℝ) : Continuous fun r => transition A r s *ᵥ v :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_transition_mulVec hA s v r).continuousAt

/-- The source of the second variational equation, `Q₂(r)(Φ(r, s) e, Φ(r, s) f)`. -/
def secondSource (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ) (s : ℝ)
    (e f : X → ℝ) (r : ℝ) : X → ℝ :=
  Q₂ r (transition A r s *ᵥ e) (transition A r s *ᵥ f)

@[tmio T, powerlib_foundation] theorem continuous_secondSource (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (s : ℝ) (e f : X → ℝ) : Continuous (secondSource A Q₂ s e f) :=
  (hQ₂.clm_apply (continuous_transition_mulVec hA s e)).clm_apply
    (continuous_transition_mulVec hA s f)

/-- The second variation `P₂(t)`: the bilinear map whose value at `(e, f)` is the value at `t` of
the solution of `ẏ = A(r) y + Q₂(r)(Φ(r, s) e, Φ(r, s) f)`, `y(s) = 0`
(`secondVariation_apply`), i.e. `P₂(t)(e, f) = ∫ₛᵗ Φ(t, r) Q₂(r)(Φ(r, s) e, Φ(r, s) f) dr`. It is
defined by its values on pairs of basis vectors. -/
def secondVariation (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (s t : ℝ) : (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ :=
  bilinOfBasis fun i j => resp A (secondSource A Q₂ s (Pi.single i 1) (Pi.single j 1)) s t

@[tmio T, powerlib_foundation] theorem secondVariation_apply (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (s t : ℝ) (e f : X → ℝ) :
    secondVariation A Q₂ s t e f = resp A (secondSource A Q₂ s e f) s t := by
  have hc := continuous_secondSource hA hQ₂ s
  let B : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] X → ℝ :=
    LinearMap.mk₂ ℝ (fun e f => resp A (secondSource A Q₂ s e f) s t)
      (fun e₁ e₂ f => by
        have h : secondSource A Q₂ s (e₁ + e₂) f =
            fun r => secondSource A Q₂ s e₁ f r + secondSource A Q₂ s e₂ f r := by
          funext r; simp [secondSource, Matrix.mulVec_add]
        simp only [h, resp_add hA (hc e₁ f) (hc e₂ f)])
      (fun c e f => by
        have h : secondSource A Q₂ s (c • e) f = fun r => c • secondSource A Q₂ s e f r := by
          funext r; simp [secondSource, Matrix.mulVec_smul]
        simp only [h, resp_smul hA (hc e f)])
      (fun e f₁ f₂ => by
        have h : secondSource A Q₂ s e (f₁ + f₂) =
            fun r => secondSource A Q₂ s e f₁ r + secondSource A Q₂ s e f₂ r := by
          funext r; simp [secondSource, Matrix.mulVec_add]
        simp only [h, resp_add hA (hc e f₁) (hc e f₂)])
      (fun c e f => by
        have h : secondSource A Q₂ s e (c • f) = fun r => c • secondSource A Q₂ s e f r := by
          funext r; simp [secondSource, Matrix.mulVec_smul]
        simp only [h, resp_smul hA (hc e f)])
  exact bilinOfBasis_eq B e f

@[tmio T, powerlib_foundation] theorem hasDerivAt_secondVariation (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (s : ℝ) (e f : X → ℝ) (r : ℝ) :
    HasDerivAt (fun r => secondVariation A Q₂ s r e f)
      (A r *ᵥ secondVariation A Q₂ s r e f + secondSource A Q₂ s e f r) r := by
  have h : (fun r => secondVariation A Q₂ s r e f) = resp A (secondSource A Q₂ s e f) s :=
    funext fun r => secondVariation_apply hA hQ₂ s r e f
  rw [h, secondVariation_apply hA hQ₂ s r e f]
  exact hasDerivAt_resp hA (continuous_secondSource hA hQ₂ s e f) s r

/-- The source of the third variational equation:
`Q₂(r)(Φ(r, s) m₀, P₂(r)(m₁, m₂)) + Q₂(r)(P₂(r)(m₀, m₁), Φ(r, s) m₂) + Q₃(r)(Φ(r, s) m)`,
trilinear in `m`; on the diagonal `m = (e, e, e)` it is
`Q₂(y₁, y₂) + Q₂(y₂, y₁) + Q₃(y₁, y₁, y₁)` with `y₁ = Φ(r, s) e`, `y₂ = P₂(r)(e, e)`. -/
def thirdSource (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ)) (s : ℝ)
    (m : Fin 3 → X → ℝ) (r : ℝ) : X → ℝ :=
  Q₂ r (transition A r s *ᵥ m 0) (secondVariation A Q₂ s r (m 1) (m 2)) +
    Q₂ r (secondVariation A Q₂ s r (m 0) (m 1)) (transition A r s *ᵥ m 2) +
    Q₃ r (fun l => transition A r s *ᵥ m l)

@[tmio T, powerlib_foundation] theorem continuous_thirdSource (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (s : ℝ) (m : Fin 3 → X → ℝ) :
    Continuous (thirdSource A Q₂ Q₃ s m) := by
  have hΦ := continuous_transition_mulVec hA s
  have hP : ∀ a b : X → ℝ, Continuous fun r => secondVariation A Q₂ s r a b := fun a b =>
    continuous_iff_continuousAt.2 fun r =>
      (hasDerivAt_secondVariation hA hQ₂ s a b r).continuousAt
  have h3 : Continuous fun r => Q₃ r (fun l => transition A r s *ᵥ m l) :=
    continuous_eval.comp (hQ₃.prodMk (continuous_pi fun l => hΦ (m l)))
  exact (((hQ₂.clm_apply (hΦ (m 0))).clm_apply (hP _ _)).add
    ((hQ₂.clm_apply (hP _ _)).clm_apply (hΦ (m 2)))).add h3

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem mulVec_update (M : Matrix X X ℝ) (m : Fin 3 → X → ℝ) (i : Fin 3)
    (z : X → ℝ) :
    (fun l => M *ᵥ update m i z l) = update (fun l => M *ᵥ m l) i (M *ᵥ z) := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [Function.update_of_ne h]

@[tmio T, powerlib_foundation] theorem thirdSource_update_add (s : ℝ) (m : Fin 3 → X → ℝ)
    (i : Fin 3) (x y : X → ℝ) (r : ℝ) :
    thirdSource A Q₂ Q₃ s (update m i (x + y)) r =
      thirdSource A Q₂ Q₃ s (update m i x) r + thirdSource A Q₂ Q₃ s (update m i y) r := by
  have h3 : Q₃ r (fun l => transition A r s *ᵥ update m i (x + y) l) =
      Q₃ r (fun l => transition A r s *ᵥ update m i x l) +
        Q₃ r (fun l => transition A r s *ᵥ update m i y l) := by
    rw [mulVec_update, mulVec_update, mulVec_update, Matrix.mulVec_add,
      (Q₃ r).map_update_add]
  simp only [thirdSource]
  rw [h3]
  fin_cases i <;> simp [Matrix.mulVec_add] <;> abel

@[tmio T, powerlib_foundation] theorem thirdSource_update_smul (s : ℝ) (m : Fin 3 → X → ℝ)
    (i : Fin 3) (c : ℝ) (x : X → ℝ) (r : ℝ) :
    thirdSource A Q₂ Q₃ s (update m i (c • x)) r = c • thirdSource A Q₂ Q₃ s (update m i x) r := by
  have h3 : Q₃ r (fun l => transition A r s *ᵥ update m i (c • x) l) =
      c • Q₃ r (fun l => transition A r s *ᵥ update m i x l) := by
    rw [mulVec_update, mulVec_update, Matrix.mulVec_smul, (Q₃ r).map_update_smul]
  simp only [thirdSource]
  rw [h3]
  fin_cases i <;> simp [Matrix.mulVec_smul, smul_add]

/-- The third variation `P₃(t)`: the trilinear map whose value at `m` is the value at `t` of the
solution of `ẏ = A(r) y + thirdSource(m)(r)`, `y(s) = 0` (`thirdVariation_apply`). It is defined
by its values on triples of basis vectors. -/
def thirdVariation (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ)) (s t : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ) :=
  multilinOfBasis fun f => resp A (thirdSource A Q₂ Q₃ s fun l => Pi.single (f l) 1) s t

@[tmio T, powerlib_foundation] theorem thirdVariation_apply (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (s t : ℝ) (m : Fin 3 → X → ℝ) :
    thirdVariation A Q₂ Q₃ s t m = resp A (thirdSource A Q₂ Q₃ s m) s t := by
  have hc := continuous_thirdSource hA hQ₂ hQ₃ s
  let M : MultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ) :=
    { toFun := fun m => resp A (thirdSource A Q₂ Q₃ s m) s t
      map_update_add' := fun {inst} m i x y => by
        obtain rfl : inst = instDecidableEqFin 3 := Subsingleton.elim _ _
        have h : thirdSource A Q₂ Q₃ s (update m i (x + y)) = fun r =>
            thirdSource A Q₂ Q₃ s (update m i x) r + thirdSource A Q₂ Q₃ s (update m i y) r :=
          funext (thirdSource_update_add s m i x y)
        simp only [h, resp_add hA (hc _) (hc _)]
      map_update_smul' := fun {inst} m i c x => by
        obtain rfl : inst = instDecidableEqFin 3 := Subsingleton.elim _ _
        have h : thirdSource A Q₂ Q₃ s (update m i (c • x)) = fun r =>
            c • thirdSource A Q₂ Q₃ s (update m i x) r :=
          funext (thirdSource_update_smul s m i c x)
        simp only [h, resp_smul hA (hc _)] }
  exact multilinOfBasis_eq M m

@[tmio T, powerlib_foundation] theorem hasDerivAt_thirdVariation (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (s : ℝ) (m : Fin 3 → X → ℝ) (r : ℝ) :
    HasDerivAt (fun r => thirdVariation A Q₂ Q₃ s r m)
      (A r *ᵥ thirdVariation A Q₂ Q₃ s r m + thirdSource A Q₂ Q₃ s m r) r := by
  have h : (fun r => thirdVariation A Q₂ Q₃ s r m) = resp A (thirdSource A Q₂ Q₃ s m) s :=
    funext fun r => thirdVariation_apply hA hQ₂ hQ₃ s r m
  rw [h, thirdVariation_apply hA hQ₂ hQ₃ s r m]
  exact hasDerivAt_resp hA (continuous_thirdSource hA hQ₂ hQ₃ s m) s r

/-! ## The cubic Taylor expansion of the flow -/

/-- The constant of the quartic remainder of the flow on a segment of length `L`, for the
Lipschitz constant `K`, the bounds `B₂ ≥ ‖Q₂‖`, `B₃ ≥ ‖Q₃‖` and the quartic Taylor constant `c₄`
of the field: with `E = e^{KL}`, `C₂ = (B₂E² + B₃E³ + c₄E⁴) L E` (the quadratic remainder),
`C₃ = (2B₂EC₂ + B₃E³ + c₄E⁴) L E` (the cubic remainder) and
`C₄ = (B₂(2EC₃ + C₂²) + 3B₃E²C₂ + c₄E⁴) L E`. -/
def taylorConst (K L B₂ B₃ c₄ : ℝ) : ℝ :=
  let E := Real.exp (K * L)
  let C₂ := (B₂ * E ^ 2 + B₃ * E ^ 3 + c₄ * E ^ 4) * L * E
  let C₃ := (2 * B₂ * E * C₂ + B₃ * E ^ 3 + c₄ * E ^ 4) * L * E
  (B₂ * (2 * E * C₃ + C₂ ^ 2) + 3 * B₃ * E ^ 2 * C₂ + c₄ * E ^ 4) * L * E

set_option maxHeartbeats 1000000 in
/-- **The cubic Taylor expansion of the flow.** Let `x_*` and `x` solve `ẋ = G(t, x)` on
`[s, t]`, `G(r, ·)` `K`-Lipschitz, and let `G` have along `x_*` the Taylor expansion
`G(r, x_* + u) = G(r, x_*) + A(r) u + Q₂(r)(u, u) + Q₃(r)(u, u, u) + R`, `‖R‖ ≤ c₄ ‖u‖⁴` for
`‖u‖ ≤ ρ`, with continuous coefficients, `‖A(r) v‖ ≤ K ‖v‖`, `‖Q₂‖ ≤ B₂`, `‖Q₃‖ ≤ B₃` on `[s, t]`
(for a field of class `C⁴`: `A = D_xG`, `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` along `x_*`). For
`e = x(s) − x_*(s)` with `‖e‖ ≤ 1` and `e^{K(t − s)} ‖e‖ ≤ ρ`:
`‖x(t) − x_*(t) − Φ(t, s) e − P₂(t)(e, e) − P₃(t)(e, e, e)‖ ≤ C₄ ‖e‖⁴`, `C₄ = taylorConst`, with
the second and third variations `P₂ = secondVariation`, `P₃ = thirdVariation`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_taylor_le {G : ℝ → (X → ℝ) → X → ℝ}
    {K : NNReal} (hK : ∀ t, LipschitzWith K (G t)) (hA : Continuous A) (hQ₂ : Continuous Q₂)
    (hQ₃ : Continuous Q₃) {s t : ℝ} (hst : s ≤ t) {B₂ B₃ c₄ ρ : ℝ} (hc₄ : 0 ≤ c₄)
    (hAK : ∀ r ∈ Icc s t, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖)
    (hB₂ : ∀ r ∈ Icc s t, ‖Q₂ r‖ ≤ B₂) (hB₃ : ∀ r ∈ Icc s t, ‖Q₃ r‖ ≤ B₃)
    {xs x : ℝ → X → ℝ} (hxs : IsIntegralCurveOn xs G (Icc s t))
    (hx : IsIntegralCurveOn x G (Icc s t))
    (hTay : ∀ r ∈ Icc s t, ∀ u, ‖u‖ ≤ ρ →
      ‖G r (xs r + u) - G r (xs r) - A r *ᵥ u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    (he1 : ‖x s - xs s‖ ≤ 1) (heρ : Real.exp (K * (t - s)) * ‖x s - xs s‖ ≤ ρ) :
    ‖x t - xs t - transition A t s *ᵥ (x s - xs s) -
        secondVariation A Q₂ s t (x s - xs s) (x s - xs s) -
        thirdVariation A Q₂ Q₃ s t (fun _ => x s - xs s)‖ ≤
      taylorConst K (t - s) B₂ B₃ c₄ * ‖x s - xs s‖ ^ 4 := by
  set e := x s - xs s with he
  set η := ‖e‖ with hη
  set L := t - s with hL
  set E := Real.exp (K * L) with hE
  have hL0 : 0 ≤ L := sub_nonneg.2 hst
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hL0)
  have hE0 : 0 ≤ E := by linarith
  have hsI : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg (Q₂ s)).trans (hB₂ s hsI)
  have hB₃0 : 0 ≤ B₃ := (norm_nonneg (Q₃ s)).trans (hB₃ s hsI)
  have hη0 : 0 ≤ η := norm_nonneg _
  have hη2 : η ^ 3 ≤ η ^ 2 := pow_le_pow_of_le_one hη0 he1 (by norm_num)
  have hη3 : η ^ 4 ≤ η ^ 3 := pow_le_pow_of_le_one hη0 he1 (by norm_num)
  have hη4 : η ^ 4 ≤ η ^ 2 := pow_le_pow_of_le_one hη0 he1 (by norm_num)
  have hexp : ∀ r ∈ Icc s t, Real.exp (K * (r - s)) ≤ E := fun r hr =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [hL]; linarith [hr.2]) K.2)
  -- the elementary bounds of the coefficients
  have hQ2b : ∀ r ∈ Icc s t, ∀ a b : X → ℝ, ‖Q₂ r a b‖ ≤ B₂ * ‖a‖ * ‖b‖ := fun r hr a b =>
    ((Q₂ r).le_opNorm₂ a b).trans (by gcongr; exact hB₂ r hr)
  have hQ3b : ∀ r ∈ Icc s t, ∀ a : X → ℝ, ‖Q₃ r (fun _ => a)‖ ≤ B₃ * ‖a‖ ^ 3 := fun r hr a => by
    refine ((Q₃ r).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact hB₃ r hr
  have hQ3d : ∀ r ∈ Icc s t, ∀ a b : X → ℝ,
      ‖Q₃ r (fun _ => a) - Q₃ r (fun _ => b)‖ ≤ 3 * B₃ * max ‖a‖ ‖b‖ ^ 2 * ‖a - b‖ := by
    intro r hr a b
    have h := (Q₃ r).norm_image_sub_le (fun _ => a) (fun _ => b)
    rw [Fintype.card_fin, pi_norm_const, pi_norm_const,
      show ((fun _ : Fin 3 => a) - fun _ => b) = fun _ => a - b from rfl, pi_norm_const] at h
    refine h.trans ?_
    have := hB₃ r hr
    have h0 : 0 ≤ max ‖a‖ ‖b‖ ^ 2 * ‖a - b‖ := by positivity
    norm_num
    nlinarith
  -- the curves of the expansion
  set u : ℝ → X → ℝ := fun r => x r - xs r with hu
  set y₁ : ℝ → X → ℝ := fun r => transition A r s *ᵥ e with hy₁
  set y₂ : ℝ → X → ℝ := fun r => secondVariation A Q₂ s r e e with hy₂
  set y₃ : ℝ → X → ℝ := fun r => thirdVariation A Q₂ Q₃ s r (fun _ => e) with hy₃
  have hxu : ∀ r, x r = xs r + u r := fun r => by simp [hu]
  have hu' : ∀ r ∈ Icc s t, HasDerivWithinAt u (G r (x r) - G r (xs r)) (Icc s t) r :=
    fun r hr => (hx r hr).sub (hxs r hr)
  have hy₁' : ∀ r, HasDerivAt y₁ (A r *ᵥ y₁ r) r := hasDerivAt_transition_mulVec hA s e
  have hy₂' : ∀ r, HasDerivAt y₂ (A r *ᵥ y₂ r + Q₂ r (y₁ r) (y₁ r)) r :=
    hasDerivAt_secondVariation hA hQ₂ s e e
  have hy₃' : ∀ r, HasDerivAt y₃
      (A r *ᵥ y₃ r + (Q₂ r (y₁ r) (y₂ r) + Q₂ r (y₂ r) (y₁ r) + Q₃ r (fun _ => y₁ r))) r :=
    hasDerivAt_thirdVariation hA hQ₂ hQ₃ s (fun _ => e)
  have hu0 : u s = e := rfl
  have hy₁0 : y₁ s = e := by simp [hy₁, LinearSystems.stateTransitionMatrix_self]
  have hy₂0 : y₂ s = 0 := by
    simp only [hy₂]; rw [secondVariation_apply hA hQ₂, resp_start]
  have hy₃0 : y₃ s = 0 := by
    simp only [hy₃]; rw [thirdVariation_apply hA hQ₂ hQ₃, resp_start]
  -- the a priori bounds of the deviation and of the linear prediction
  have hub : ∀ r ∈ Icc s t, ‖u r‖ ≤ E * η := by
    intro r hr
    have h := dist_le_of_isIntegralCurveOn_Icc hK hx hxs r hr
    rw [dist_eq_norm, dist_eq_norm] at h
    calc ‖u r‖ = ‖x r - xs r‖ := rfl
      _ ≤ ‖x s - xs s‖ * Real.exp (K * (r - s)) := h
      _ ≤ η * E := mul_le_mul_of_nonneg_left (hexp r hr) hη0
      _ = E * η := mul_comm _ _
  have hy₁b : ∀ r ∈ Icc s t, ‖y₁ r‖ ≤ E * η := by
    intro r hr
    have h := norm_le_of_hasDerivWithinAt (w := y₁) K.2 le_rfl
      (fun q _ => (hy₁' q).hasDerivWithinAt)
      (fun q hq => by simpa using hAK q (Ico_subset_Icc_self hq) (y₁ q))
      (by rw [hy₁0]) r hr
    rw [zero_mul, add_zero] at h
    exact h.trans_eq (mul_comm _ _)
  -- the Taylor remainder of the field along the deviation
  set R : ℝ → X → ℝ := fun r => G r (xs r + u r) - G r (xs r) - A r *ᵥ u r -
    Q₂ r (u r) (u r) - Q₃ r (fun _ => u r) with hRdef
  have hR : ∀ r ∈ Icc s t, ‖R r‖ ≤ c₄ * (E * η) ^ 4 := fun r hr =>
    (hTay r hr (u r) ((hub r hr).trans heρ)).trans
      (by gcongr; exact hub r hr)
  -- step 1: the quadratic remainder `a = u − y₁`
  set C₂ := (B₂ * E ^ 2 + B₃ * E ^ 3 + c₄ * E ^ 4) * L * E with hC₂
  have ha : ∀ r ∈ Icc s t, ‖u r - y₁ r‖ ≤ C₂ * η ^ 2 := by
    set ε := (B₂ * E ^ 2 + B₃ * E ^ 3 + c₄ * E ^ 4) * η ^ 2 with hε
    have hd : ∀ r ∈ Icc s t, HasDerivWithinAt (fun r => u r - y₁ r)
        (A r *ᵥ (u r - y₁ r) + (Q₂ r (u r) (u r) + Q₃ r (fun _ => u r) + R r)) (Icc s t) r := by
      intro r hr
      convert (hu' r hr).sub (hy₁' r).hasDerivWithinAt using 1
      rw [hxu r]
      simp only [hRdef, Matrix.mulVec_sub]
      abel
    have hbd : ∀ r ∈ Ico s t, ‖A r *ᵥ (u r - y₁ r) +
        (Q₂ r (u r) (u r) + Q₃ r (fun _ => u r) + R r)‖ ≤ K * ‖u r - y₁ r‖ + ε := by
      intro r hr
      have hr' := Ico_subset_Icc_self hr
      have h1 := hQ2b r hr' (u r) (u r)
      have h2 := hQ3b r hr' (u r)
      have h3 := hR r hr'
      have hb := hub r hr'
      have hP : ‖u r‖ ^ 2 ≤ (E * η) ^ 2 := by gcongr
      have hP3 : ‖u r‖ ^ 3 ≤ (E * η) ^ 3 := by gcongr
      calc _ ≤ ‖A r *ᵥ (u r - y₁ r)‖ + (‖Q₂ r (u r) (u r)‖ + ‖Q₃ r (fun _ => u r)‖ + ‖R r‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)))
        _ ≤ K * ‖u r - y₁ r‖ + (B₂ * (E * η) ^ 2 + B₃ * (E * η) ^ 3 + c₄ * (E * η) ^ 4) := by
            gcongr
            · exact hAK r hr' _
            · calc ‖Q₂ r (u r) (u r)‖ ≤ B₂ * ‖u r‖ * ‖u r‖ := h1
                _ = B₂ * ‖u r‖ ^ 2 := by ring
                _ ≤ B₂ * (E * η) ^ 2 := by gcongr
            · exact h2.trans (by gcongr)
        _ ≤ K * ‖u r - y₁ r‖ + ε := by
            rw [hε]
            have e3 : B₃ * (E * η) ^ 3 ≤ B₃ * E ^ 3 * η ^ 2 := by
              rw [mul_pow, ← mul_assoc]; gcongr
            have e4 : c₄ * (E * η) ^ 4 ≤ c₄ * E ^ 4 * η ^ 2 := by
              rw [mul_pow, ← mul_assoc]; gcongr
            nlinarith
    have hε0 : 0 ≤ ε := by positivity
    intro r hr
    have h := norm_le_of_hasDerivWithinAt K.2 hε0 hd hbd
      (by rw [hu0, hy₁0, sub_self, norm_zero]) r hr
    calc ‖u r - y₁ r‖ ≤ (0 + ε * (t - s)) * Real.exp (K * (t - s)) := h
      _ = C₂ * η ^ 2 := by rw [hε, hC₂]; ring
  have hC₂0 : 0 ≤ C₂ := by positivity
  -- step 2: the cubic remainder `b = u − y₁ − y₂`
  set C₃ := (2 * B₂ * E * C₂ + B₃ * E ^ 3 + c₄ * E ^ 4) * L * E with hC₃
  have hb : ∀ r ∈ Icc s t, ‖u r - y₁ r - y₂ r‖ ≤ C₃ * η ^ 3 := by
    set ε := (2 * B₂ * E * C₂ + B₃ * E ^ 3 + c₄ * E ^ 4) * η ^ 3 with hε
    have hd : ∀ r ∈ Icc s t, HasDerivWithinAt (fun r => u r - y₁ r - y₂ r)
        (A r *ᵥ (u r - y₁ r - y₂ r) + (Q₂ r (u r - y₁ r) (u r) + Q₂ r (y₁ r) (u r - y₁ r) +
          Q₃ r (fun _ => u r) + R r)) (Icc s t) r := by
      intro r hr
      convert ((hu' r hr).sub (hy₁' r).hasDerivWithinAt).sub (hy₂' r).hasDerivWithinAt using 1
      rw [hxu r]
      simp only [hRdef, Matrix.mulVec_sub, map_sub, _root_.sub_apply]
      abel
    have hbd : ∀ r ∈ Ico s t, ‖A r *ᵥ (u r - y₁ r - y₂ r) + (Q₂ r (u r - y₁ r) (u r) +
        Q₂ r (y₁ r) (u r - y₁ r) + Q₃ r (fun _ => u r) + R r)‖ ≤
        K * ‖u r - y₁ r - y₂ r‖ + ε := by
      intro r hr
      have hr' := Ico_subset_Icc_self hr
      have h1 := hQ2b r hr' (u r - y₁ r) (u r)
      have h1' := hQ2b r hr' (y₁ r) (u r - y₁ r)
      have h2 := hQ3b r hr' (u r)
      have h3 := hR r hr'
      have hu1 := hub r hr'
      have hy1 := hy₁b r hr'
      have ha1 := ha r hr'
      calc _ ≤ ‖A r *ᵥ (u r - y₁ r - y₂ r)‖ + (‖Q₂ r (u r - y₁ r) (u r)‖ +
            ‖Q₂ r (y₁ r) (u r - y₁ r)‖ + ‖Q₃ r (fun _ => u r)‖ + ‖R r‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans
              (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
                le_rfl)))
        _ ≤ K * ‖u r - y₁ r - y₂ r‖ + (B₂ * (C₂ * η ^ 2) * (E * η) +
            B₂ * (E * η) * (C₂ * η ^ 2) + B₃ * (E * η) ^ 3 + c₄ * (E * η) ^ 4) := by
            gcongr
            · exact hAK r hr' _
            · exact h1.trans (by gcongr)
            · exact h1'.trans (by gcongr)
            · exact h2.trans (by gcongr)
        _ ≤ K * ‖u r - y₁ r - y₂ r‖ + ε := by
            rw [hε]
            have e4 : c₄ * (E * η) ^ 4 ≤ c₄ * E ^ 4 * η ^ 3 := by
              rw [mul_pow, ← mul_assoc]; gcongr
            nlinarith
    have hε0 : 0 ≤ ε := by positivity
    intro r hr
    have h := norm_le_of_hasDerivWithinAt K.2 hε0 hd hbd
      (by rw [hu0, hy₁0, hy₂0, sub_self, sub_zero, norm_zero]) r hr
    calc ‖u r - y₁ r - y₂ r‖ ≤ (0 + ε * (t - s)) * Real.exp (K * (t - s)) := h
      _ = C₃ * η ^ 3 := by rw [hε, hC₃]; ring
  have hC₃0 : 0 ≤ C₃ := by positivity
  -- step 3: the quartic remainder `z = u − y₁ − y₂ − y₃`
  set ε := (B₂ * (2 * E * C₃ + C₂ ^ 2) + 3 * B₃ * E ^ 2 * C₂ + c₄ * E ^ 4) * η ^ 4 with hε
  have hd : ∀ r ∈ Icc s t, HasDerivWithinAt (fun r => u r - y₁ r - y₂ r - y₃ r)
      (A r *ᵥ (u r - y₁ r - y₂ r - y₃ r) + (Q₂ r (y₁ r) (u r - y₁ r - y₂ r) +
        Q₂ r (u r - y₁ r - y₂ r) (y₁ r) + Q₂ r (u r - y₁ r) (u r - y₁ r) +
        (Q₃ r (fun _ => u r) - Q₃ r (fun _ => y₁ r)) + R r)) (Icc s t) r := by
    intro r hr
    convert (((hu' r hr).sub (hy₁' r).hasDerivWithinAt).sub (hy₂' r).hasDerivWithinAt).sub
      (hy₃' r).hasDerivWithinAt using 1
    rw [hxu r]
    simp only [hRdef, Matrix.mulVec_sub, map_sub, _root_.sub_apply]
    abel
  have hbd : ∀ r ∈ Ico s t, ‖A r *ᵥ (u r - y₁ r - y₂ r - y₃ r) +
      (Q₂ r (y₁ r) (u r - y₁ r - y₂ r) + Q₂ r (u r - y₁ r - y₂ r) (y₁ r) +
        Q₂ r (u r - y₁ r) (u r - y₁ r) + (Q₃ r (fun _ => u r) - Q₃ r (fun _ => y₁ r)) + R r)‖ ≤
      K * ‖u r - y₁ r - y₂ r - y₃ r‖ + ε := by
    intro r hr
    have hr' := Ico_subset_Icc_self hr
    have h1 := hQ2b r hr' (y₁ r) (u r - y₁ r - y₂ r)
    have h1' := hQ2b r hr' (u r - y₁ r - y₂ r) (y₁ r)
    have h1'' := hQ2b r hr' (u r - y₁ r) (u r - y₁ r)
    have h2 := hQ3d r hr' (u r) (y₁ r)
    have h3 := hR r hr'
    have hu1 := hub r hr'
    have hy1 := hy₁b r hr'
    have ha1 := ha r hr'
    have hb1 := hb r hr'
    have hmax : max ‖u r‖ ‖y₁ r‖ ≤ E * η := max_le hu1 hy1
    calc _ ≤ ‖A r *ᵥ (u r - y₁ r - y₂ r - y₃ r)‖ + (‖Q₂ r (y₁ r) (u r - y₁ r - y₂ r)‖ +
          ‖Q₂ r (u r - y₁ r - y₂ r) (y₁ r)‖ + ‖Q₂ r (u r - y₁ r) (u r - y₁ r)‖ +
          ‖Q₃ r (fun _ => u r) - Q₃ r (fun _ => y₁ r)‖ + ‖R r‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans
            (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)))
      _ ≤ K * ‖u r - y₁ r - y₂ r - y₃ r‖ + (B₂ * (E * η) * (C₃ * η ^ 3) +
          B₂ * (C₃ * η ^ 3) * (E * η) + B₂ * (C₂ * η ^ 2) * (C₂ * η ^ 2) +
          3 * B₃ * (E * η) ^ 2 * (C₂ * η ^ 2) + c₄ * (E * η) ^ 4) := by
          gcongr
          · exact hAK r hr' _
          · exact h1.trans (by gcongr)
          · exact h1'.trans (by gcongr)
          · exact h1''.trans (by gcongr)
          · exact h2.trans (by gcongr)
      _ = K * ‖u r - y₁ r - y₂ r - y₃ r‖ + ε := by rw [hε]; ring
  have hε0 : 0 ≤ ε := by positivity
  have h := norm_le_of_hasDerivWithinAt K.2 hε0 hd hbd
    (by rw [hu0, hy₁0, hy₂0, hy₃0, sub_self, sub_zero, sub_zero, norm_zero]) t ⟨hst, le_rfl⟩
  calc ‖u t - y₁ t - y₂ t - y₃ t‖ ≤ (0 + ε * (t - s)) * Real.exp (K * (t - s)) := h
    _ = taylorConst K (t - s) B₂ B₃ c₄ * η ^ 4 := by
      rw [hε]
      simp only [taylorConst]
      rw [← hL, ← hE, ← hC₂, ← hC₃]
      ring

/-- The second variation by variation of constants:
`P₂(t)(e, f) = ∫ₛᵗ Φ(t, r) Q₂(r)(Φ(r, s) e, Φ(r, s) f) dr`. -/
@[tmio T, powerlib_foundation] theorem secondVariation_eq_integral (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (s t : ℝ) (e f : X → ℝ) :
    secondVariation A Q₂ s t e f =
      ∫ r in s..t, transition A t r *ᵥ Q₂ r (transition A r s *ᵥ e) (transition A r s *ᵥ f) := by
  rw [secondVariation_apply hA hQ₂, resp_eq_integral]
  rfl

/-- The third variation by variation of constants:
`P₃(t)(m) = ∫ₛᵗ Φ(t, r) [Q₂(r)(Φ(r, s) m₀, P₂(r)(m₁, m₂)) + Q₂(r)(P₂(r)(m₀, m₁), Φ(r, s) m₂) +
Q₃(r)(Φ(r, s) m)] dr`. -/
@[tmio T, powerlib_foundation] theorem thirdVariation_eq_integral (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (s t : ℝ) (m : Fin 3 → X → ℝ) :
    thirdVariation A Q₂ Q₃ s t m = ∫ r in s..t, transition A t r *ᵥ
      (Q₂ r (transition A r s *ᵥ m 0) (secondVariation A Q₂ s r (m 1) (m 2)) +
        Q₂ r (secondVariation A Q₂ s r (m 0) (m 1)) (transition A r s *ᵥ m 2) +
        Q₃ r (fun l => transition A r s *ᵥ m l)) := by
  rw [thirdVariation_apply hA hQ₂ hQ₃, resp_eq_integral]
  rfl

/-- **The cubic Taylor expansion of the period map.** Let `G` be continuous and `K`-Lipschitz in
the state, `x_*` a global solution with `x_*(T) = x_*(0)`, and let `G` have along `x_*` on
`[0, T]` the Taylor expansion of `norm_sub_taylor_le`. Then the period map
`P(ξ) = x(T; 0, ξ)` (`FlowDerivative.periodMap`) satisfies, with `p = x_*(0)`,
`M = Φ(T, 0) = monodromy A T 0`, `P₂ = P₂(T)`, `P₃ = P₃(T)`:
`‖P(p + e) − p − M e − P₂(e, e) − P₃(e, e, e)‖ ≤ C₄ ‖e‖⁴` for `‖e‖ ≤ min 1 (ρ e^{−KT})`,
`C₄ = taylorConst K T B₂ B₃ c₄`. -/
@[tmio T, powerlib_foundation] theorem periodMap_taylor {G : ℝ → (X → ℝ) → X → ℝ}
    {K : NNReal} (hGc : Continuous (uncurry G)) (hK : ∀ t, LipschitzWith K (G t))
    (hA : Continuous A) (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {T : ℝ} (hT : 0 ≤ T)
    {B₂ B₃ c₄ ρ : ℝ} (hc₄ : 0 ≤ c₄) (hAK : ∀ r ∈ Icc 0 T, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖)
    (hB₂ : ∀ r ∈ Icc 0 T, ‖Q₂ r‖ ≤ B₂) (hB₃ : ∀ r ∈ Icc 0 T, ‖Q₃ r‖ ≤ B₃)
    {xs : ℝ → X → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hper : xs T = xs 0)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ →
      ‖G r (xs r + u) - G r (xs r) - A r *ᵥ u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    (e : X → ℝ) (he : ‖e‖ ≤ min 1 (ρ / Real.exp (K * T))) :
    ‖FlowDerivative.periodMap hGc hK T (xs 0 + e) - xs 0 - monodromy A T 0 *ᵥ e -
        secondVariation A Q₂ 0 T e e - thirdVariation A Q₂ Q₃ 0 T (fun _ => e)‖ ≤
      taylorConst K T B₂ B₃ c₄ * ‖e‖ ^ 4 := by
  set x := FlowDerivative.flow hGc hK 0 (xs 0 + e) with hxdef
  have hx0 : x 0 - xs 0 = e := by
    rw [hxdef, FlowDerivative.flow_start]; abel
  have hxI : IsIntegralCurveOn x G (Icc 0 T) :=
    (FlowDerivative.flow_solution hGc hK 0 _).mono Icc_subset_Ici_self
  have hxsI : IsIntegralCurveOn xs G (Icc 0 T) := fun r _ => (hxs r).hasDerivWithinAt
  have hE : 0 < Real.exp (K * T) := Real.exp_pos _
  have he1 : ‖x 0 - xs 0‖ ≤ 1 := by rw [hx0]; exact he.trans (min_le_left _ _)
  have heρ : Real.exp (K * (T - 0)) * ‖x 0 - xs 0‖ ≤ ρ := by
    rw [hx0, sub_zero]
    have := he.trans (min_le_right _ _)
    rw [le_div_iff₀ hE] at this
    linarith
  have h := norm_sub_taylor_le hK hA hQ₂ hQ₃ hT hc₄ hAK hB₂ hB₃ hxsI hxI hTay he1 heρ
  rw [hx0, sub_zero, hper] at h
  rw [monodromy, zero_add]
  exact h

end powerlib.Periodic.PeriodMapTaylor
