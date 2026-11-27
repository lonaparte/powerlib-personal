import theorem.Periodic.DegenerateFlipReduction

/-! # The degenerate flip from the Taylor coefficients of the map

`theorem/Periodic/DegenerateFlipReduction.lean` decides a fixed point `p` of a map `P` with a
simple multiplier `−1` and vanishing flip coefficient by the sign of `c₅ + 3c₂c₄ − 2c₂⁴`, where
the `cⱼ` are the coefficients of the scalar map along a candidate curve, taken as a hypothesis.
This module derives them from the multilinear Taylor coefficients of `P` alone. With
`P(p + e) = p + M e + P₂(e, e) + P₃(e³) + P₄(e⁴) + P₅(e⁵) + O(‖e‖⁶)`, `M v = −v`, `w ∘ M = −w`,
`w v = 1`, `Q e = e − (w e) v`, and `f'(a) b = Σᵢ f(a, …, b, …, a)` (`b` in slot `i`, Mathlib's
`ContinuousMultilinearMap.linearDeriv`), the polynomial candidate
`η(t) = t² k₂ + t³ k₃ + t⁴ k₄` of the projection method solves the homological equations

* `(I − M) k₂ = Q P₂(v, v)`,
* `(−I − M) k₃ = Q n₃ + 2c₂ k₂`, `w k₃ = 0`,
* `(I − M) k₄ = Q n₄ − (c₂² − 2c₃) k₂ − 3c₂ k₃`,

(the coefficients of `t²`, `t³`, `t⁴` of the invariance defect: `(λʲ − M) kⱼ` with `λ = −1`
against `Q nⱼ` and the terms of `η(s(t))`, `s(t) = −t + c₂ t² + c₃ t³ + O(t⁴)`; `−I − M` is
singular on `v`, whence the normalization `w k₃ = 0`), where `nⱼ` is the coefficient of `tʲ` in
`N(t v + η(t))`, `N e = P(p + e) − p − M e`:

* `n₂ = P₂(v, v)`, `n₃ = P₃(v³) + P₂(v, k₂) + P₂(k₂, v)`,
* `n₄ = P₄(v⁴) + P₃'(v) k₂ + P₂(v, k₃) + P₂(k₃, v) + P₂(k₂, k₂)`,
* `n₅ = P₅(v⁵) + P₄'(v) k₂ + P₃'(v) k₃ + P₃'(k₂) v + P₂(v, k₄) + P₂(k₄, v) + P₂(k₂, k₃) +
  P₂(k₃, k₂)`,

and `cⱼ = w nⱼ`. Then the invariance defect is `O(t⁵)` (`defect_expansion_five`), the centre
manifold lies within `O(x⁵)` of the candidate (`exists_reduced_map_near_candidate`, the
approximation theorem through the adapted coordinates of `theorem/Periodic/FlipReduction.lean`),
and the restricted map is `r(x) = −x + c₂ x² + c₃ x³ + c₄ x⁴ + c₅ x⁵ + O(x⁶)`
(`exists_reduced_map_five`): the Taylor polynomial changes by `O(x · x⁵)` between the centre
manifold and the candidate, and the remainders are `O(x⁶)` (`isBigO_sub_of_taylor_five`), so no
Lipschitz flatness of `N` (the hypothesis `hN` of `DegenerateFlipReduction`) is needed. With
`c₂² + c₃ = 0` the sign of `c₅ + 3c₂c₄ − 2c₂⁴` decides (`theorem/Map/DegenerateFlip.lean`):
positive — locally asymptotically, not exponentially, stable; negative — unstable. `c₂` and `c₃`
are the coefficients `a`, `b` of the flip coefficient `a² + b` of `FlipReduction`. For symmetric
`Pⱼ = DʲP(p)/j!` one has `Pⱼ'(v) k = j Pⱼ(v^{j−1}, k)` and `P₃'(k₂) v = 3 P₃(k₂, k₂, v)`.

Scope.
* The setting of `theorem/Periodic/FlipReduction.lean`: the map semantics on
  `ℝⁿ = EuclideanSpace ℝ (Fin n)`, a map `P` with fixed point `p` and strict derivative `M`
  there, the spectral hypothesis in projector form (`M v = −v`, `w ∘ M = −w`, `w v = 1`, a power
  of `M + v wᵀ` of norm below one, or a Schur stable matrix `Lm` with `Linear.op Lm = M + v wᵀ`).
* The fifth-order expansion with remainder `K ‖e‖⁶` on `‖e‖ ≤ ρ₀` is a **hypothesis** (a map of
  class `C⁶`); `P₂` is a continuous bilinear map, `P₃`, `P₄`, `P₅` are continuous multilinear
  maps on `Fin 3`, `Fin 4`, `Fin 5` (`ContinuousMultilinearMap`), none assumed symmetric; the
  cubic part is the hypothesis of `FlipReduction`. For a period map the expansion is to be
  derived from the field (to third order it is `periodMap_taylor` of
  `theorem/Periodic/PeriodMapTaylor.lean`); it is not derived here.
* `k₂, k₃, k₄` are any solutions of the homological equations; they exist
  (`exists_homological`), `k₂` and `k₄` are unique and `k₃` is unique in `ker w`.
* `c₅ + 3c₂c₄ − 2c₂⁴ = 0` is not decided (the next odd order is needed, and no finite order
  suffices in general: `Map.flat_jet_undecided`).
* Generic; nothing here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.4 (the projection
method: homological equations for the coefficients of a centre manifold and the restricted
normalized map from the multilinear Taylor coefficients) and §9.5 (degenerate flip); Kuznetsov
and Meijer, "Numerical normal forms for codim 2 bifurcations of fixed points with at most two
critical eigenvalues", SIAM J. Sci. Comput. 26 (2005) (the fifth-order coefficient of the
degenerate flip from the multilinear forms of the map); Carr, *Applications of Centre Manifold
Theory* (1981), Ch. 2 (Theorem 3, the approximation theorem); the open item of
`theorem/Periodic/DegenerateFlipReduction.lean` (Scope: the expression of the coefficients
through the multilinear Taylor coefficients of `P` "is not derived here").

Results.
* Multilinear maps along a curve: `isBigO_multilin`, `isBigO_multilin_sub`,
  `isBigO_map_add_sub_linearDeriv` (`f(x + β) − f(x) − f'(x) β = O(β²)`), `multilin_diag_smul`,
  `linearDeriv_diag_smul`, `trilin_diag_add` (`f(a + b) = f(a) + f'(a) b + f'(b) a + f(b)` for
  three slots), `isBigO_diag`.
* The candidate and its coefficients: `graphJet` (`η`), `curveCoeff₃`, `curveCoeff₄`,
  `curveCoeff₅` (`n₃`, `n₄`, `n₅`); `isBigO_pow_of_le`;
  `isBigO_taylor_five` (the remainder along a curve), `isBigO_sub_of_taylor_five` (`N(α) − N(β) =
  O(g⁶)` for `α − β = O(g⁵)`), **`curve_expansion`** (`N(t v + η(t)) = Σⱼ tʲ nⱼ + O(t⁶)`),
  `powers_expansion` (the powers of `s(t)`).
* The reduction: `exists_reduced_map_near_candidate` (the centre manifold within `O(x^q)` of a
  candidate of defect `O(t^q)`, without a regularity hypothesis on `N`), `scalar_expansion`
  (`w(P(p + t v + η(t)) − p) = −t + Σⱼ cⱼ tʲ + O(t⁶)`), **`defect_expansion_five`** (the
  homological equations give the defect `O(t⁵)`), `exists_homological` (they are solvable).
* **The theorems**: `exists_reduced_map_five` (the restricted map
  `−x + c₂x² + c₃x³ + c₄x⁴ + c₅x⁵ + O(x⁶)` with the closed-form coefficients),
  `localAsymptoticStable_of_degenerateFlip_taylor` (`c₂² + c₃ = 0`, `c₅ + 3c₂c₄ − 2c₂⁴ > 0`:
  locally asymptotically, not exponentially, stable), `unstable_of_degenerateFlip_taylor`
  (`< 0`: unstable), and their matrix forms
  `localAsymptoticStable_of_degenerateFlip_taylor_matrix`,
  `unstable_of_degenerateFlip_taylor_matrix`.

Corrections.
None: an extension (the coefficients of the degenerate flip from the Taylor data of the map,
which `theorem/Periodic/DegenerateFlipReduction.lean` took as a hypothesis, and the removal of
its Lipschitz flatness hypothesis when a fifth-order expansion is known).

Family and connection conclusions.
None: static evidence on maps (the period map of a periodic orbit).
-/

noncomputable section

open Filter Topology Asymptotics

namespace powerlib.Periodic.FlipReduction

/-! ## Multilinear maps along a curve -/

section Multilinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A continuous multilinear map of a bounded argument: `f(α) = O(gᶜᵃʳᵈ)` when `α = O(g)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_multilin {ι Z : Type*} [Fintype ι] {l : Filter Z}
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) {α : Z → ι → E} {g : Z → ℝ}
    (hα : α =O[l] g) : (fun z => f (α z)) =O[l] fun z => g z ^ Fintype.card ι := by
  have h1 : (fun z => f (α z)) =O[l] fun z => ‖α z‖ ^ Fintype.card ι :=
    IsBigO.of_bound ‖f‖ (Eventually.of_forall fun z => by
      rw [norm_pow, norm_norm]
      exact f.le_opNorm_mul_pow_card_of_le le_rfl)
  exact h1.trans (hα.norm_left.pow _)

/-- The difference of a continuous multilinear map at two arguments:
`f(α) − f(β) = O(g^{card − 1} g')` when `α, β = O(g)` and `α − β = O(g')`. -/
@[tmio T, powerlib_foundation] theorem isBigO_multilin_sub {ι Z : Type*} [Fintype ι]
    {l : Filter Z} (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) {α β : Z → ι → E}
    {g g' : Z → ℝ} (hα : α =O[l] g) (hβ : β =O[l] g) (hαβ : (fun z => α z - β z) =O[l] g') :
    (fun z => f (α z) - f (β z)) =O[l] fun z => g z ^ (Fintype.card ι - 1) * g' z := by
  have h1 : (fun z => f (α z) - f (β z)) =O[l]
      fun z => (‖α z‖ + ‖β z‖) ^ (Fintype.card ι - 1) * ‖α z - β z‖ :=
    IsBigO.of_bound (‖f‖ * Fintype.card ι) (Eventually.of_forall fun z => by
      have := f.norm_image_sub_le (α z) (β z)
      have hm : max ‖α z‖ ‖β z‖ ^ (Fintype.card ι - 1) ≤
          (‖α z‖ + ‖β z‖) ^ (Fintype.card ι - 1) :=
        pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _))
          (max_le (le_add_of_nonneg_right (norm_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))) _
      rw [Real.norm_of_nonneg (by positivity)]
      calc _ ≤ _ := this
        _ ≤ ‖f‖ * Fintype.card ι * (‖α z‖ + ‖β z‖) ^ (Fintype.card ι - 1) * ‖α z - β z‖ := by
          gcongr
        _ = _ := by ring)
  exact h1.trans (IsBigO.mul (IsBigO.pow (hα.norm_left.add hβ.norm_left) _) hαβ.norm_left)

/-- **The first-order expansion of a multilinear map with a quadratic remainder:**
`f(x + β) − f(x) − f'(x) β = O(g²)` when `β = O(g)` and `‖β‖ ≤ 1` eventually, where
`f'(x) β = Σᵢ f(x with β in slot i)` is `ContinuousMultilinearMap.linearDeriv`. -/
@[tmio T, powerlib_foundation] theorem isBigO_map_add_sub_linearDeriv {ι Z : Type*} [Fintype ι]
    [DecidableEq ι] {l : Filter Z} (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F)
    (x : ι → E) {β : Z → ι → E} {g : Z → ℝ} (hβ : β =O[l] g) (hβ1 : ∀ᶠ z in l, ‖β z‖ ≤ 1) :
    (fun z => f (x + β z) - f x - f.linearDeriv x (β z)) =O[l] fun z => g z ^ 2 := by
  have key : ∀ z, f (x + β z) - f x - f.linearDeriv x (β z) =
      ∑ s ∈ Finset.univ.filter (fun s : Finset ι => 2 ≤ s.card), f (s.piecewise (β z) x) := by
    intro z
    have := f.toMultilinearMap.map_add_eq_map_add_linearDeriv_add x (β z)
    simp only [ContinuousMultilinearMap.coe_coe, MultilinearMap.linearDeriv_apply] at this
    rw [this, ContinuousMultilinearMap.linearDeriv_apply]
    abel
  simp_rw [key]
  refine IsBigO.fun_sum fun s hs => ?_
  have hs2 : 2 ≤ s.card := (Finset.mem_filter.mp hs).2
  refine IsBigO.trans ?_ (hβ.norm_left.pow 2)
  refine IsBigO.of_bound (‖f‖ * ∏ i ∈ Finset.univ \ s, ‖x i‖) ?_
  filter_upwards [hβ1] with z hz
  rw [Real.norm_of_nonneg (by positivity)]
  refine (f.le_opNorm _).trans ?_
  have hprod : ∏ i, ‖s.piecewise (β z) x i‖ =
      (∏ i ∈ s, ‖β z i‖) * ∏ i ∈ Finset.univ \ s, ‖x i‖ := by
    have e : ∏ i, ‖s.piecewise (β z) x i‖ =
        ∏ i, s.piecewise (fun i => ‖β z i‖) (fun i => ‖x i‖) i :=
      Finset.prod_congr rfl fun i _ => by by_cases hi : i ∈ s <;> simp [hi]
    rw [e, Finset.prod_piecewise, Finset.univ_inter]
  rw [hprod]
  have h1 : ∏ i ∈ s, ‖β z i‖ ≤ ‖β z‖ ^ 2 := by
    refine (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      fun i _ => norm_le_pi_norm (β z) i).trans ?_
    rw [Finset.prod_const]
    exact pow_le_pow_of_le_one (norm_nonneg _) hz hs2
  have h2 : 0 ≤ ∏ i ∈ Finset.univ \ s, ‖x i‖ := by positivity
  calc ‖f‖ * ((∏ i ∈ s, ‖β z i‖) * ∏ i ∈ Finset.univ \ s, ‖x i‖)
      ≤ ‖f‖ * (‖β z‖ ^ 2 * ∏ i ∈ Finset.univ \ s, ‖x i‖) := by gcongr
    _ = _ := by ring

/-- A multilinear map on the diagonal is homogeneous: `f(t a, …, t a) = tʲ f(a, …, a)`. -/
@[tmio T, powerlib_foundation] theorem multilin_diag_smul {j : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) (t : ℝ) (a : E) :
    f (fun _ => t • a) = t ^ j • f (fun _ => a) := by
  have := f.map_smul_univ (fun _ => t) (fun _ => a)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this

/-- The derivative of a multilinear map on the diagonal is homogeneous of degree `j` in the base
point: `f'(t a, …, t a)(b, …, b) = tʲ f'(a, …, a)(b, …, b)` for `j + 1` slots. -/
@[tmio T, powerlib_foundation] theorem linearDeriv_diag_smul {j : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F) (t : ℝ) (a b : E) :
    f.linearDeriv (fun _ => t • a) (fun _ => b) =
      t ^ j • f.linearDeriv (fun _ => a) (fun _ => b) := by
  simp only [ContinuousMultilinearMap.linearDeriv_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : Function.update (fun _ => t • a) i b =
      fun k => Function.update (fun _ => t) i 1 k • Function.update (fun _ => a) i b k := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [e, f.map_smul_univ, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.card_sdiff, Finset.prod_const]

/-- **A trilinear map on the diagonal of a sum:**
`f(a + b) = f(a) + f'(a) b + f'(b) a + f(b)` (`f'(a) b` is the sum over the slots of `f` with `b`
in one slot and `a` in the other two). -/
@[tmio T, powerlib_foundation] theorem trilin_diag_add
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) F) (a b : E) :
    f (fun _ => a + b) = f (fun _ => a) + f.linearDeriv (fun _ => a) (fun _ => b) +
      f.linearDeriv (fun _ => b) (fun _ => a) + f (fun _ => b) := by
  have h3 : ∀ c : E, (fun _ : Fin 3 => c) = ![c, c, c] := fun c => by
    funext i; fin_cases i <;> rfl
  have s0 : ∀ x x' y z : E, f ![x + x', y, z] = f ![x, y, z] + f ![x', y, z] := fun x x' y z =>
    f.cons_add _ x x'
  have s1 : ∀ x y y' z : E, f ![x, y + y', z] = f ![x, y, z] + f ![x, y', z] := fun x y y' z => by
    have := f.map_update_add ![x, y, z] 1 y y'
    have e : ∀ c, Function.update ![x, y, z] 1 c = ![x, c, z] := fun c => by
      funext i; fin_cases i <;> rfl
    rwa [e, e, e] at this
  have s2 : ∀ x y z z' : E, f ![x, y, z + z'] = f ![x, y, z] + f ![x, y, z'] := fun x y z z' => by
    have := f.map_update_add ![x, y, z] 2 z z'
    have e : ∀ c, Function.update ![x, y, z] 2 c = ![x, y, c] := fun c => by
      funext i; fin_cases i <;> rfl
    rwa [e, e, e] at this
  have u : ∀ c d : E, f.linearDeriv (fun _ => c) (fun _ => d) =
      f ![d, c, c] + f ![c, d, c] + f ![c, c, d] := fun c d => by
    rw [ContinuousMultilinearMap.linearDeriv_apply, Fin.sum_univ_three]
    have e0 : Function.update (fun _ : Fin 3 => c) 0 d = ![d, c, c] := by
      funext i; fin_cases i <;> rfl
    have e1 : Function.update (fun _ : Fin 3 => c) 1 d = ![c, d, c] := by
      funext i; fin_cases i <;> rfl
    have e2 : Function.update (fun _ : Fin 3 => c) 2 d = ![c, c, d] := by
      funext i; fin_cases i <;> rfl
    rw [e0, e1, e2]
  rw [u, u, h3, h3 a, h3 b, s0, s1, s1, s2, s2, s2, s2]
  abel

omit [NormedSpace ℝ E] in
/-- The constant tuple of a bounded function is bounded: `(α, …, α) = O(g)` when `α = O(g)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_diag {ι Z : Type*} [Fintype ι] {l : Filter Z}
    {α : Z → E} {g : Z → ℝ} (hα : α =O[l] g) : (fun z => fun _ : ι => α z) =O[l] g :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [one_mul]; exact pi_norm_const_le (α z))).trans hα

end Multilinear

/-! ## The polynomial candidate and the expansion of the map along it -/

section Jet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The polynomial candidate graph `η(t) = t² k₂ + t³ k₃ + t⁴ k₄`. -/
def graphJet (k₂ k₃ k₄ : E) (t : ℝ) : E := t ^ 2 • k₂ + t ^ 3 • k₃ + t ^ 4 • k₄

/-- The coefficient of `t³` in `N(t v + η(t))`: `P₃(v, v, v) + P₂(v, k₂) + P₂(k₂, v)`. -/
def curveCoeff₃ (P₂ : E →L[ℝ] E →L[ℝ] E) (P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E)
    (v k₂ : E) : E :=
  P₃ (fun _ => v) + (P₂ v k₂ + P₂ k₂ v)

/-- The coefficient of `t⁴` in `N(t v + η(t))`:
`P₄(v⁴) + P₃'(v) k₂ + P₂(v, k₃) + P₂(k₃, v) + P₂(k₂, k₂)`, with `P₃'(v) k₂` the sum of `P₃` over
the three placements of `k₂` among `v, v`. -/
def curveCoeff₄ (P₂ : E →L[ℝ] E →L[ℝ] E) (P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E)
    (P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E) (v k₂ k₃ : E) : E :=
  P₄ (fun _ => v) + P₃.linearDeriv (fun _ => v) (fun _ => k₂) + (P₂ v k₃ + P₂ k₃ v) + P₂ k₂ k₂

/-- The coefficient of `t⁵` in `N(t v + η(t))`: `P₅(v⁵) + P₄'(v) k₂ + P₃'(v) k₃ + P₃'(k₂) v +
P₂(v, k₄) + P₂(k₄, v) + P₂(k₂, k₃) + P₂(k₃, k₂)` (`P₃'(k₂) v`: `v` in one slot, `k₂` in the
other two). -/
def curveCoeff₅ (P₂ : E →L[ℝ] E →L[ℝ] E) (P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E)
    (P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E)
    (P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => E) E) (v k₂ k₃ k₄ : E) : E :=
  P₅ (fun _ => v) + P₄.linearDeriv (fun _ => v) (fun _ => k₂) +
    (P₃.linearDeriv (fun _ => v) (fun _ => k₃) + P₃.linearDeriv (fun _ => k₂) (fun _ => v)) +
    (P₂ v k₄ + P₂ k₄ v) + (P₂ k₂ k₃ + P₂ k₃ k₂)

/-- Near `0`, `tʲ = O(tⁱ)` for `i ≤ j`. -/
@[tmio T, powerlib_foundation] theorem isBigO_pow_of_le {i j : ℕ} (hij : i ≤ j) :
    (fun t : ℝ => t ^ j) =O[𝓝 0] fun t => t ^ i :=
  Dynamics.isBigO_pow_of_tendsto (s := fun t : ℝ => t) tendsto_id hij

/-- The Taylor remainder of order six along a function of order one: if
`N e − P₂(e, e) − P₃(e³) − P₄(e⁴) − P₅(e⁵)` is bounded by `K ‖e‖⁶` near `0`, `α = O(g)` and
`g → 0`, then the remainder along `α` is `O(g⁶)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_taylor_five {N : E → E}
    {P₂ : E →L[ℝ] E →L[ℝ] E} {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => E) E} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e) - P₄ (fun _ => e) -
      P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {Z : Type*} {l : Filter Z} {g : Z → ℝ} (hg : Tendsto g l (𝓝 0)) {α : Z → E}
    (hα : α =O[l] g) :
    (fun z => N (α z) - P₂ (α z) (α z) - P₃ (fun _ => α z) - P₄ (fun _ => α z) -
      P₅ (fun _ => α z)) =O[l] fun z => g z ^ 6 := by
  have hR0 : (fun e => N e - P₂ e e - P₃ (fun _ => e) - P₄ (fun _ => e) - P₅ (fun _ => e))
      =O[𝓝 (0 : E)] fun e => ‖e‖ ^ 6 := by
    refine IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) hρ₀] with e he
    rw [Metric.mem_closedBall, dist_zero_right] at he
    rw [norm_pow, norm_norm]
    exact hTay e he
  exact (hR0.comp_tendsto (hα.trans_tendsto hg)).trans (hα.norm_left.pow 6)

/-- **The map at two nearby points**, from the fifth-order expansion alone: if `α, β = O(g)`,
`α − β = O(g⁵)` and `g → 0`, then `N(α) − N(β) = O(g⁶)` (the Taylor polynomial changes by
`O(g · g⁵)`, the remainders are `O(g⁶)`; no derivative of `N` is used). -/
@[tmio T, powerlib_foundation] theorem isBigO_sub_of_taylor_five {N : E → E}
    {P₂ : E →L[ℝ] E →L[ℝ] E} {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => E) E} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e) - P₄ (fun _ => e) -
      P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {Z : Type*} {l : Filter Z} {g : Z → ℝ} (hg : Tendsto g l (𝓝 0)) {α β : Z → E}
    (hα : α =O[l] g) (hβ : β =O[l] g) (hαβ : (fun z => α z - β z) =O[l] fun z => g z ^ 5) :
    (fun z => N (α z) - N (β z)) =O[l] fun z => g z ^ 6 := by
  have hc : ∀ c : ℕ, 2 ≤ c → (fun z => g z ^ (c - 1) * g z ^ 5) =O[l] fun z => g z ^ 6 :=
    fun c hc => (Dynamics.isBigO_pow_of_tendsto hg (by omega : 6 ≤ c - 1 + 5)).congr_left
      fun z => by rw [pow_add]
  have hαβ' : (fun z => (fun _ : Fin 3 => α z) - fun _ => β z) =O[l] fun z => g z ^ 5 :=
    (isBigO_diag hαβ).congr_left fun z => by funext i; simp
  have h2 : (fun z => P₂ (α z) (α z) - P₂ (β z) (β z)) =O[l] fun z => g z ^ 6 := by
    have := (isBigO_bilin P₂ hαβ hα).add
      ((isBigO_bilin P₂ hβ hαβ).congr_right fun z => mul_comm _ _)
    refine (this.congr_left fun z => ?_).congr_right fun z => ?_
    · simp only [map_sub, sub_apply]; abel
    · ring
  have h3 := (isBigO_multilin_sub P₃ (isBigO_diag hα) (isBigO_diag hβ) hαβ').trans
    (hc _ (by simp))
  have h4 := (isBigO_multilin_sub P₄ (isBigO_diag hα) (isBigO_diag hβ)
    ((isBigO_diag hαβ).congr_left fun z => by funext i; simp)).trans (hc _ (by simp))
  have h5 := (isBigO_multilin_sub P₅ (isBigO_diag hα) (isBigO_diag hβ)
    ((isBigO_diag hαβ).congr_left fun z => by funext i; simp)).trans (hc _ (by simp))
  have hRα := isBigO_taylor_five hρ₀ hTay hg hα
  have hRβ := isBigO_taylor_five hρ₀ hTay hg hβ
  refine ((((hRα.sub hRβ).add h2).add h3).add h4 |>.add h5).congr_left fun z => ?_
  abel

/-- **The map along the polynomial candidate.** If `N e = P₂(e, e) + P₃(e³) + P₄(e⁴) + P₅(e⁵) +
O(‖e‖⁶)`, then along `e(t) = t v + t² k₂ + t³ k₃ + t⁴ k₄`
`N(e(t)) = t² P₂(v, v) + t³ n₃ + t⁴ n₄ + t⁵ n₅ + O(t⁶)` with the coefficients `curveCoeff₃`,
`curveCoeff₄`, `curveCoeff₅`. -/
@[tmio T, powerlib_foundation] theorem curve_expansion {N : E → E} {P₂ : E →L[ℝ] E →L[ℝ] E}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => E) E} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e) - P₄ (fun _ => e) -
      P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    (v k₂ k₃ k₄ : E) :
    (fun t : ℝ => N (t • v + graphJet k₂ k₃ k₄ t) - (t ^ 2 • P₂ v v +
      t ^ 3 • curveCoeff₃ P₂ P₃ v k₂ + t ^ 4 • curveCoeff₄ P₂ P₃ P₄ v k₂ k₃ +
      t ^ 5 • curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄)) =O[𝓝 0] fun t => t ^ 6 := by
  -- the curve as `t (v + t z(t))`
  have he : ∀ t : ℝ, t • v + graphJet k₂ k₃ k₄ t = t • (v + t • (k₂ + t • k₃ + t ^ 2 • k₄)) :=
    fun t => by simp only [graphJet, smul_add, smul_smul]; module
  -- elementary bounds
  have hid : (fun t : ℝ => t) =O[𝓝 0] fun t => t ^ 1 := by simpa using isBigO_refl _ _
  have hsc : ∀ (i : ℕ) (c : E), (fun t : ℝ => t ^ i • c) =O[𝓝 0] fun t => t ^ i :=
    fun i c => isBigO_smul_const (isBigO_refl _ _) c
  have hO1 : ∀ {f : ℝ → E} {c : E}, Tendsto f (𝓝 0) (𝓝 c) → f =O[𝓝 0] fun _ => (1 : ℝ) :=
    fun h => h.isBigO_one ℝ
  have hone : ∀ c : E, (fun _ : ℝ => c) =O[𝓝 0] fun _ => (1 : ℝ) := fun c =>
    hO1 tendsto_const_nhds
  have ht0 : Tendsto (fun t : ℝ => t ^ 1) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 1).tendsto (0 : ℝ)
  have hd : (fun t : ℝ => t • k₃ + t ^ 2 • k₄) =O[𝓝 0] fun t => t ^ 1 :=
    (isBigO_smul_const hid k₃).add ((hsc 2 k₄).trans (isBigO_pow_of_le (by norm_num)))
  have hz : (fun t : ℝ => k₂ + t • k₃ + t ^ 2 • k₄) =O[𝓝 0] fun _ => (1 : ℝ) := by
    have := (hone k₂).add (hO1 (hd.trans_tendsto ht0))
    simpa only [add_assoc] using this
  have hb : (fun t : ℝ => t • (k₂ + t • k₃ + t ^ 2 • k₄)) =O[𝓝 0] fun t => t ^ 1 := by
    have := hid.smul hz
    simpa using this
  have hb0 : Tendsto (fun t : ℝ => t • (k₂ + t • k₃ + t ^ 2 • k₄)) (𝓝 0) (𝓝 0) :=
    hb.trans_tendsto ht0
  have hvb : (fun t : ℝ => v + t • (k₂ + t • k₃ + t ^ 2 • k₄)) =O[𝓝 0] fun _ => (1 : ℝ) :=
    (hone v).add (hO1 hb0)
  have he1 : (fun t : ℝ => t • (v + t • (k₂ + t • k₃ + t ^ 2 • k₄))) =O[𝓝 0] fun t => t ^ 1 := by
    have := hid.smul hvb
    simpa using this
  have he0 : Tendsto (fun t : ℝ => t • (v + t • (k₂ + t • k₃ + t ^ 2 • k₄))) (𝓝 0) (𝓝 0) :=
    he1.trans_tendsto ht0
  have hcurve : (fun t : ℝ => t • v + graphJet k₂ k₃ k₄ t) =O[𝓝 0] fun t => t ^ 1 :=
    he1.congr_left fun t => (he t).symm
  have hd0 : Tendsto (fun t : ℝ => t • k₃ + t ^ 2 • k₄) (𝓝 0) (𝓝 0) := hd.trans_tendsto ht0
  have hpow6 : ∀ i j : ℕ, i + j = 6 →
      (fun t : ℝ => t ^ i * t ^ j) =O[𝓝 0] fun t => t ^ 6 := fun i j h =>
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by rw [← pow_add, h, one_mul])
  -- the Taylor remainder
  have hR : (fun t : ℝ => N (t • v + graphJet k₂ k₃ k₄ t) -
      P₂ (t • v + graphJet k₂ k₃ k₄ t) (t • v + graphJet k₂ k₃ k₄ t) -
      P₃ (fun _ => t • v + graphJet k₂ k₃ k₄ t) - P₄ (fun _ => t • v + graphJet k₂ k₃ k₄ t) -
      P₅ (fun _ => t • v + graphJet k₂ k₃ k₄ t)) =O[𝓝 0] fun t => t ^ 6 := by
    refine (isBigO_taylor_five hρ₀ hTay ht0 hcurve).trans
      (IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_))
    rw [one_mul, ← pow_mul]
  -- the quintic term
  have h5 : (fun t : ℝ => P₅ (fun _ => t • v + graphJet k₂ k₃ k₄ t) - t ^ 5 • P₅ (fun _ => v))
      =O[𝓝 0] fun t => t ^ 6 := by
    have hdiff := isBigO_multilin_sub P₅ (isBigO_diag (ι := Fin 5) hvb)
      (isBigO_diag (ι := Fin 5) (hone v))
      ((isBigO_diag (ι := Fin 5) hb).congr_left fun t => by funext i; simp)
    refine ((isBigO_refl (fun t : ℝ => t ^ 5) _).smul hdiff).congr' ?_ ?_
    · exact Eventually.of_forall fun t => by
        simp only [he t, multilin_diag_smul, smul_sub]
    · exact Eventually.of_forall fun t => by simp only [smul_eq_mul]; ring
  -- the quartic term
  have h4 : (fun t : ℝ => P₄ (fun _ => t • v + graphJet k₂ k₃ k₄ t) -
      (t ^ 4 • P₄ (fun _ => v) + t ^ 5 • P₄.linearDeriv (fun _ => v) (fun _ => k₂)))
      =O[𝓝 0] fun t => t ^ 6 := by
    have hβ := isBigO_diag (ι := Fin 4) hb
    have hβ1 : ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖(fun _ : Fin 4 => t • (k₂ + t • k₃ + t ^ 2 • k₄))‖ ≤ 1 := by
      have := (hβ.trans_tendsto ht0).eventually (Metric.closedBall_mem_nhds 0 one_pos)
      filter_upwards [this] with t ht
      simpa using ht
    have hA := isBigO_map_add_sub_linearDeriv P₄ (fun _ => v) hβ hβ1
    have hL := ((P₄.linearDeriv (fun _ => v)).isBigO_comp _ _).trans
      (isBigO_diag (ι := Fin 4) hd)
    have hsum := hA.add ((hid.smul hL).trans (IsBigO.of_bound 1 (Eventually.of_forall
      fun t => by simp only [smul_eq_mul, one_mul, norm_mul, norm_pow]; ring_nf; exact le_rfl)))
    refine ((isBigO_refl (fun t : ℝ => t ^ 4) _).smul hsum).congr' ?_ ?_
    · refine Eventually.of_forall fun t => ?_
      simp only [he t, multilin_diag_smul]
      have e1 : (fun _ : Fin 4 => v) + (fun _ => t • (k₂ + t • k₃ + t ^ 2 • k₄)) =
          fun _ => v + t • (k₂ + t • k₃ + t ^ 2 • k₄) := rfl
      have e2 : (fun _ : Fin 4 => t • (k₂ + t • k₃ + t ^ 2 • k₄)) =
          t • ((fun _ => k₂) + fun _ => t • k₃ + t ^ 2 • k₄) := by
        funext i; simp [add_assoc]
      rw [e1, e2, map_smul, map_add]
      module
    · exact Eventually.of_forall fun t => by simp only [smul_eq_mul]; ring
  -- the cubic term
  have h3 : (fun t : ℝ => P₃ (fun _ => t • v + graphJet k₂ k₃ k₄ t) -
      (t ^ 3 • P₃ (fun _ => v) + t ^ 4 • P₃.linearDeriv (fun _ => v) (fun _ => k₂) +
        t ^ 5 • (P₃.linearDeriv (fun _ => v) (fun _ => k₃) +
          P₃.linearDeriv (fun _ => k₂) (fun _ => v)))) =O[𝓝 0] fun t => t ^ 6 := by
    -- `a ↦ P₃'(a) v` through the diagonal of a sum
    have hswap : ∀ a : E, P₃.linearDeriv (fun _ => a) (fun _ => v) =
        P₃ (fun _ => a + v) - P₃ (fun _ => a) - P₃.linearDeriv (fun _ => v) (fun _ => a) -
          P₃ (fun _ => v) := fun a => by
      rw [trilin_diag_add]; abel
    have hk : (fun t : ℝ => (fun _ : Fin 3 => k₂ + t • k₃ + t ^ 2 • k₄) - fun _ => k₂)
        =O[𝓝 0] fun t => t ^ 1 :=
      (isBigO_diag (ι := Fin 3) hd).congr_left fun t => by funext i; simp [add_assoc]
    have hkv : (fun t : ℝ => (fun _ : Fin 3 => k₂ + t • k₃ + t ^ 2 • k₄ + v) - fun _ => k₂ + v)
        =O[𝓝 0] fun t => t ^ 1 :=
      (isBigO_diag (ι := Fin 3) hd).congr_left fun t => by funext i; simp; abel
    have hD1 := isBigO_multilin_sub P₃ (isBigO_diag (ι := Fin 3) (hz.add (hone v)))
      (isBigO_diag (ι := Fin 3) (hone (k₂ + v))) hkv
    have hD2 := isBigO_multilin_sub P₃ (isBigO_diag (ι := Fin 3) hz)
      (isBigO_diag (ι := Fin 3) (hone k₂)) hk
    have hD3 := ((P₃.linearDeriv (fun _ => v)).isBigO_comp _ _).trans hk
    have hLz : (fun t : ℝ => P₃.linearDeriv (fun _ => k₂ + t • k₃ + t ^ 2 • k₄) (fun _ => v) -
        P₃.linearDeriv (fun _ => k₂) (fun _ => v)) =O[𝓝 0] fun t => t ^ 1 := by
      have := ((hD1.sub hD2).trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
        simp))).sub hD3
      refine this.congr_left fun t => ?_
      rw [hswap, hswap, map_sub]
      abel
    have hP3z := isBigO_multilin P₃ (isBigO_diag (ι := Fin 3) hz)
    have hsum := ((hsc 6 (P₃.linearDeriv (fun _ => v) (fun _ => k₄))).add
      (((isBigO_refl (fun t : ℝ => t ^ 5) _).smul hLz).trans (hpow6 5 1 rfl))).add
      (((isBigO_refl (fun t : ℝ => t ^ 6) _).smul hP3z).trans (IsBigO.of_bound 1
        (Eventually.of_forall fun t => by simp)))
    refine hsum.congr_left fun t => ?_
    have e1 : P₃ (fun _ => t • v + graphJet k₂ k₃ k₄ t) =
        t ^ 3 • (P₃ (fun _ => v) + t • P₃.linearDeriv (fun _ => v)
          (fun _ => k₂ + t • k₃ + t ^ 2 • k₄) +
          t ^ 2 • P₃.linearDeriv (fun _ => k₂ + t • k₃ + t ^ 2 • k₄) (fun _ => v) +
          t ^ 3 • P₃ (fun _ => k₂ + t • k₃ + t ^ 2 • k₄)) := by
      rw [he t, multilin_diag_smul, trilin_diag_add, linearDeriv_diag_smul, multilin_diag_smul]
      have e2 : (fun _ : Fin 3 => t • (k₂ + t • k₃ + t ^ 2 • k₄)) =
          t • (fun _ => k₂ + t • k₃ + t ^ 2 • k₄) := rfl
      rw [e2, map_smul]
    rw [e1]
    rw [show P₃.linearDeriv (fun _ => v) (fun _ => k₂ + t • k₃ + t ^ 2 • k₄) =
        P₃.linearDeriv (fun _ => v) ((fun _ => k₂) + t • (fun _ => k₃) + t ^ 2 • (fun _ => k₄))
        from rfl]
    simp only [map_add, map_smul]
    module
  -- the quadratic term
  have h2 : (fun t : ℝ => P₂ (t • v + graphJet k₂ k₃ k₄ t) (t • v + graphJet k₂ k₃ k₄ t) -
      (t ^ 2 • P₂ v v + t ^ 3 • (P₂ v k₂ + P₂ k₂ v) + t ^ 4 • ((P₂ v k₃ + P₂ k₃ v) + P₂ k₂ k₂) +
        t ^ 5 • ((P₂ v k₄ + P₂ k₄ v) + (P₂ k₂ k₃ + P₂ k₃ k₂)))) =O[𝓝 0] fun t => t ^ 6 := by
    have hsum := (hsc 6 (P₂ k₂ k₄ + P₂ k₄ k₂)).add
      (((isBigO_refl (fun t : ℝ => t ^ 4) _).smul (isBigO_bilin P₂ hd hd)).trans
        (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
          simp only [smul_eq_mul, one_mul, norm_mul, norm_pow]; ring_nf; exact le_rfl)))
    refine hsum.congr_left fun t => ?_
    simp only [graphJet, map_add, map_smul, add_apply,
      FunLike.coe_smul, Pi.smul_apply]
    module
  -- the sum
  refine ((((hR.add h2).add h3).add h4).add h5).congr_left fun t => ?_
  simp only [curveCoeff₃, curveCoeff₄, curveCoeff₅, smul_add]
  abel

/-- **The powers of the reduced coordinate.** If `s(t) = −t + c₂ t² + c₃ t³ + σ(t)` with
`σ = O(t⁴)`, then `s² = t² − 2c₂ t³ + (c₂² − 2c₃) t⁴ + O(t⁵)`, `s³ = −t³ + 3c₂ t⁴ + O(t⁵)` and
`s⁴ = t⁴ + O(t⁵)`. -/
@[tmio T, powerlib_foundation] theorem powers_expansion (c₂ c₃ : ℝ) {σ : ℝ → ℝ}
    (hσ : σ =O[𝓝 0] fun t => t ^ 4) :
    (fun t => (-t + c₂ * t ^ 2 + c₃ * t ^ 3 + σ t) ^ 2 -
        (t ^ 2 - 2 * c₂ * t ^ 3 + (c₂ ^ 2 - 2 * c₃) * t ^ 4)) =O[𝓝 0] (fun t => t ^ 5) ∧
      (fun t => (-t + c₂ * t ^ 2 + c₃ * t ^ 3 + σ t) ^ 3 - (-t ^ 3 + 3 * c₂ * t ^ 4))
        =O[𝓝 0] (fun t => t ^ 5) ∧
      (fun t => (-t + c₂ * t ^ 2 + c₃ * t ^ 3 + σ t) ^ 4 - t ^ 4) =O[𝓝 0] (fun t => t ^ 5) := by
  set u : ℝ → ℝ := fun t => -t + c₂ * t ^ 2 + c₃ * t ^ 3 with hu
  have hid : (fun t : ℝ => t) =O[𝓝 0] fun t => t ^ 1 := by simpa using isBigO_refl _ _
  have hu1 : u =O[𝓝 0] fun t => t ^ 1 :=
    ((hid.neg_left.add ((isBigO_pow_of_le (by norm_num : 1 ≤ 2)).const_mul_left c₂)).add
      ((isBigO_pow_of_le (by norm_num : 1 ≤ 3)).const_mul_left c₃))
  have hσ1 : σ =O[𝓝 0] fun t => t ^ 1 := hσ.trans (isBigO_pow_of_le (by norm_num))
  have hmul : ∀ {f g : ℝ → ℝ}, f =O[𝓝 0] (fun t => t ^ 1) → g =O[𝓝 0] (fun t => t ^ 1) →
      (fun t => f t * g t) =O[𝓝 0] fun t => t ^ 1 := fun hf hg =>
    (hf.mul hg).trans ((isBigO_pow_of_le (by norm_num : 1 ≤ 2)).congr_left fun t => by ring)
  have hq : ∀ q : ℝ → ℝ, Continuous q →
      (fun t => t ^ 5 * q t) =O[𝓝 0] fun t => t ^ 5 := fun q hq =>
    ((isBigO_refl (fun t : ℝ => t ^ 5) _).mul ((hq.tendsto 0).isBigO_one ℝ)).congr_right
      fun t => by ring
  have hσmul : ∀ {g : ℝ → ℝ}, g =O[𝓝 0] (fun t => t ^ 1) →
      (fun t => σ t * g t) =O[𝓝 0] fun t => t ^ 5 := fun hg =>
    (hσ.mul hg).congr_right fun t => by ring
  refine ⟨?_, ?_, ?_⟩
  · have := (hq (fun t => 2 * c₂ * c₃ + c₃ ^ 2 * t) (by fun_prop)).add
      (hσmul ((hu1.const_mul_left 2).add hσ1))
    refine this.congr_left fun t => ?_
    simp only [hu]; ring
  · have hb : (fun t => 3 * (u t * u t) + 3 * (u t * σ t) + σ t * σ t) =O[𝓝 0]
        fun t => t ^ 1 :=
      (((hmul hu1 hu1).const_mul_left 3).add ((hmul hu1 hσ1).const_mul_left 3)).add
        (hmul hσ1 hσ1)
    have := (hq (fun t => c₂ ^ 3 * t + 3 * c₂ ^ 2 * c₃ * t ^ 2 - 3 * c₂ ^ 2 +
      3 * c₂ * c₃ ^ 2 * t ^ 3 - 6 * c₂ * c₃ * t + c₃ ^ 3 * t ^ 4 - 3 * c₃ ^ 2 * t ^ 2 + 3 * c₃)
      (by fun_prop)).add (hσmul hb)
    refine this.congr_left fun t => ?_
    simp only [hu]; ring
  · have hb : (fun t => 4 * (u t * u t * u t) + 6 * (u t * u t * σ t) +
        4 * (u t * σ t * σ t) + σ t * σ t * σ t) =O[𝓝 0] fun t => t ^ 1 :=
      ((((hmul (hmul hu1 hu1) hu1).const_mul_left 4).add
        ((hmul (hmul hu1 hu1) hσ1).const_mul_left 6)).add
        ((hmul (hmul hu1 hσ1) hσ1).const_mul_left 4)).add (hmul (hmul hσ1 hσ1) hσ1)
    have := (hq (fun t => c₂ ^ 4 * t ^ 3 + 4 * c₂ ^ 3 * c₃ * t ^ 4 - 4 * c₂ ^ 3 * t ^ 2 +
      6 * c₂ ^ 2 * c₃ ^ 2 * t ^ 5 - 12 * c₂ ^ 2 * c₃ * t ^ 3 + 6 * c₂ ^ 2 * t +
      4 * c₂ * c₃ ^ 3 * t ^ 6 - 12 * c₂ * c₃ ^ 2 * t ^ 4 + 12 * c₂ * c₃ * t ^ 2 - 4 * c₂ +
      c₃ ^ 4 * t ^ 7 - 4 * c₃ ^ 3 * t ^ 5 + 6 * c₃ ^ 2 * t ^ 3 - 4 * c₃ * t)
      (by fun_prop)).add (hσmul hb)
    refine this.congr_left fun t => ?_
    simp only [hu]; ring

end Jet

/-! ## The centre manifold near a candidate curve -/

section Reduction

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

variable {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {v : EuclideanSpace ℝ (Fin n)} {w : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}

/-- **The centre manifold near a candidate curve.** In the setting of `exists_reduced_map` (`P`
fixes `p`, strict derivative `M`, `M v = −v`, `w ∘ M = −w`, `w v = 1`, a power of `M + v wᵀ` of
norm below one), let `η : ℝ → ℝⁿ` (`η(0) = 0`, `η'(0) = 0` strictly, `w ∘ η = 0`) describe a
candidate curve `t ↦ p + t v + η(t)` whose invariance defect
`Q(P(p + t v + η t) − p) − η(w(P(p + t v + η t) − p))` is `O(t^q)` (`Q e = e − (w e) v`,
`q ≥ 1`). Then there are a map `r : ℝ¹ → ℝ¹` (the map restricted to a centre manifold, in the
coordinate `w`) and the stable coordinate `y : ℝ¹ → ℝⁿ` of that centre manifold, with
`y(x) = η(x) + O(‖x‖^q)` and `r(x) = −x + w N(x v + y(x))` near `0`
(`N e = P(p + e) − p − M e`), whose local asymptotic stability gives that of `P` at `p`, and
which is Lyapunov stable exactly when `P` is at `p`. No regularity of `N` beyond the strict
derivative `0` at `0` is assumed (compare `exists_reduced_map_of_candidate`, which also bounds
`r` against the candidate's map under a Lipschitz flatness hypothesis). -/
@[tmio T, powerlib_foundation] theorem exists_reduced_map_near_candidate {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflate M v w ^ m‖ < 1) {η : ℝ → ℝⁿ} (hη : HasStrictDerivAt η 0 0) (hη0 : η 0 = 0)
    (hwη : ∀ t, w (η t) = 0) {q : ℕ} (hq : 1 ≤ q)
    (hD : (fun t : ℝ => specProj v w (P (p + (t • v + η t)) - p) -
      η (w (P (p + (t • v + η t)) - p))) =O[𝓝 0] fun t => t ^ q) :
    ∃ r : ℝ¹ → ℝ¹, ∃ y : ℝ¹ → ℝⁿ,
      (fun x : ℝ¹ => y x - η (x 0)) =O[𝓝 0] (fun x => ‖x‖ ^ q) ∧
      (∀ᶠ x in 𝓝 0, r x 0 = -x 0 + w (nonlin P p M (x 0 • v + y x))) ∧
      (Map.LocalAsymptoticStable r 0 → Map.LocalAsymptoticStable P p) ∧
      (Map.LyapunovStable r 0 ↔ Map.LyapunovStable P p) := by
  set Ld := deflate M v w with hLdef
  obtain ⟨θ, hθ0, hθ1, hθm⟩ := exists_rate hm hLm
  -- the size of the nonlinearities
  have hεr : 0 < (1 - θ) / (2 * ((q : ℝ) + 2)) := div_pos (by linarith) (by positivity)
  let ε : NNReal := ⟨(1 - θ) / (2 * ((q : ℝ) + 2)), hεr.le⟩
  have hεe : (ε : ℝ) = (1 - θ) / (2 * ((q : ℝ) + 2)) := rfl
  have hε0 : 0 < ε := by rw [← NNReal.coe_pos, hεe]; exact hεr
  have hqε : ((q : ℝ) + 2) * ε = (1 - θ) / 2 := by rw [hεe]; field_simp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hεpos : (0 : ℝ) < ε := hεr
  have h3ε : 3 * (ε : ℝ) ≤ (1 - θ) / 2 := by nlinarith
  have hgap : θ + 3 * ε < 1 := by linarith
  have hθ2 : θ + 2 * ε < 1 := by linarith
  have hεa : (ε : ℝ) < 1 := by linarith
  have hκ1 : θ + ε < 1 - ε := by linarith
  have hκq : θ + ε < (1 - ε) ^ q := by
    have hb := one_add_mul_le_pow (a := -(ε : ℝ)) (by linarith) q
    rw [← sub_eq_add_neg] at hb
    nlinarith
  -- coordinates and the linear part
  set Φ := coordMap M v w m θ with hΦ
  set Ψ := coordInv (n := n) v hm with hΨ
  set B := orbitShift m hm θ Ld with hBdef
  set A : ℝ¹ →L[ℝ] ℝ¹ := -ContinuousLinearMap.id ℝ ℝ¹ with hAdef
  have hAs : Function.Surjective A := fun x => ⟨-x, by simp [hAdef]⟩
  have hA : ∀ x, 1 * ‖x‖ ≤ ‖A x‖ := fun x => by simp [hAdef]
  have hB : ∀ u, ‖B u‖ ≤ θ * ‖u‖ := norm_orbitShift_le hm hθ0 hθm
  -- the cut-off nonlinearity
  obtain ⟨hN', hN0⟩ := nonlin_spec hP hPp
  set ε' : NNReal := ε / ((‖Φ‖₊ + 1) * (‖Ψ‖₊ + 1)) with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨ρ₁, hρ₁, Nc, hNcl, hNc0, hNcN⟩ :=
    Map.CenterManifold.exists_lipschitz_cutoff hN' hN0 hε'0
  set f := cutF M v w hm θ Nc with hfdef
  set g := cutG M v w hm θ Nc with hgdef
  have hK : ‖Φ‖₊ * ε' * ‖Ψ‖₊ ≤ ε := by
    rw [hε', ← NNReal.coe_le_coe]
    push_cast
    have ha := norm_nonneg Φ
    have hb := norm_nonneg Ψ
    have hε := ε.coe_nonneg
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hε ha, mul_nonneg hε hb, mul_nonneg (mul_nonneg hε ha) hb]
  have hfl : LipschitzWith ε f := (lipschitzWith_cut hm θ hNcl).1.weaken hK
  have hgl : LipschitzWith ε g := (lipschitzWith_cut hm θ hNcl).2.weaken hK
  have hf0 : f 0 = 0 := by simp [hfdef, cutF, hNc0]
  have hg0 : g 0 = 0 := by simp [hgdef, cutG, hNc0]
  -- the centre manifold, its range and its graph
  set h := Map.CenterManifold.centreGraph A B f g with hhdef
  obtain ⟨hh, hh0, hinv⟩ :=
    Map.CenterManifold.centreGraph_spec hAs hA hB hθ0.le hfl hgl hf0 hg0 (by simpa using hgap)
  set T : ℝⁿ →L[ℝ] (Fin m → ℝⁿ) := (orbitEmb m θ Ld).comp (specProj v w) with hTdef
  set Kr : Submodule ℝ (Fin m → ℝⁿ) := LinearMap.range (T : ℝⁿ →ₗ[ℝ] (Fin m → ℝⁿ)) with hKr
  have hKc : IsClosed (Kr : Set (Fin m → ℝⁿ)) := Submodule.closed_of_finiteDimensional _
  have hBK : ∀ y ∈ Kr, B y ∈ Kr := by
    rintro _ ⟨z, rfl⟩
    refine ⟨M z, ?_⟩
    simp only [hTdef, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply, hBdef]
    rw [orbitShift_orbitEmb hm hθ0.ne', (deflate_specProj hv hw hwv z).1]
  have hgK : ∀ x, ∀ y ∈ Kr, g (x, y) ∈ Kr := fun x y _ => ⟨Nc (Ψ (x, y)), rfl⟩
  have hhK : ∀ x, h x ∈ Kr := fun x =>
    Map.CenterManifold.centreGraph_mem hKc hBK hgK hAs hA hB hθ0.le hfl hgl hf0 hg0
      (by simpa using hgap) x
  have hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x) := fun x => by
    obtain ⟨z, hz⟩ := hhK x
    rw [← hz]
    exact coordMap_coordInv hwv hm θ x z
  -- the map read in the coordinates
  have hG : ∀ e, ‖e‖ < ρ₁ →
      Φ ((fun e => P (p + e) - p) e) = Map.CenterManifold.splitMap A B f g (Φ e) :=
    fun e he => coordMap_conj hv hw hwv hm hθ0.ne' (hNcN e he.le)
  -- identities along a curve `e = t v + y`, `w y = 0`
  have hPe : ∀ e, P (p + e) - p = M e + nonlin P p M e := fun e => by simp only [nonlin]; abel
  have hwP : ∀ (t : ℝ) (y : ℝ¹ → ℝⁿ) (x : ℝ¹), w (y x) = 0 →
      w (P (p + (t • v + y x)) - p) = -t + w (nonlin P p M (t • v + y x)) := fun t y x hy => by
    rw [hPe, map_add, hw]
    simp [map_add, map_smul, hwv, hy]
  -- the candidate graph in the coordinates
  set φ : ℝ¹ → (Fin m → ℝⁿ) := fun x => orbitEmb m θ Ld (η (x 0)) with hφdef
  have hφ0 : φ 0 = 0 := by simp [hφdef, hη0]
  have hp0 : HasStrictFDerivAt (fun x : ℝ¹ => x 0)
      (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) 0 := by
    have e : (fun x : ℝ¹ => x 0) = ⇑(EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) := by
      funext x; simp
    rw [e]
    exact ContinuousLinearMap.hasStrictFDerivAt (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ)
  have hφ : HasStrictFDerivAt φ (0 : ℝ¹ →L[ℝ] (Fin m → ℝⁿ)) 0 := by
    have h2 : HasStrictFDerivAt η (0 : ℝ →L[ℝ] ℝⁿ) ((fun x : ℝ¹ => x 0) 0) := by
      have := hη.hasStrictFDerivAt
      simpa using this
    have h3 := (orbitEmb m θ Ld).hasStrictFDerivAt.comp (0 : ℝ¹) (h2.comp (0 : ℝ¹) hp0)
    convert h3 using 1
    ext x
    simp
  have hx0lim : Tendsto (fun x : ℝ¹ => x 0) (𝓝 0) (𝓝 0) := by
    simpa using hp0.continuousAt.tendsto
  have hu1' : (fun x : ℝ¹ => x 0) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    simpa using isBigO_coord_pow 1
  have hηO : (fun x : ℝ¹ => η (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    have h1 : η =O[𝓝 0] fun t : ℝ => t := by
      have := hη.hasDerivAt.isLittleO
      simp only [hη0, sub_zero, smul_zero] at this
      exact this.isBigO
    exact (h1.comp_tendsto hx0lim).trans hu1'
  have heη : (fun x : ℝ¹ => x 0 • v + η (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ 1 :=
    (isBigO_smul_const hu1' v).add hηO
  have hnorm0 : Tendsto (fun x : ℝ¹ => ‖x‖ ^ 1) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_norm_zero (E := ℝ¹)).pow 1
  have hevη : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + η (x 0)‖ ≤ ρ₁ := by
    have := (heη.trans_tendsto hnorm0).eventually (Metric.closedBall_mem_nhds 0 hρ₁)
    filter_upwards [this] with x hx
    simpa using hx
  -- its invariance defect is `−T D` with the defect `D` in `ℝⁿ`
  have hDc : (fun x => φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)) =O[𝓝 0]
      fun x => ‖x‖ ^ q := by
    have hD' := ((hD.comp_tendsto hx0lim).trans (isBigO_coord_pow q))
    refine (((orbitEmb m θ Ld).isBigO_comp _ _).trans hD').neg_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hevη] with x hx1
    have hΨφ : coordInv v hm (x, φ x) = x 0 • v + η (x 0) := by
      rw [coordInv_apply]
      show x 0 • v + orbitEmb m θ Ld (η (x 0)) ⟨0, hm⟩ = _
      rw [orbitEmb_zero]
    have hNe := hNcN _ hx1
    have hfφ : f (x, φ x) = centreCoord w (nonlin P p M (x 0 • v + η (x 0))) := by
      simp only [hfdef, cutF, hΨφ, hNe]; rfl
    have hgφ : g (x, φ x) =
        orbitEmb m θ Ld (specProj v w (nonlin P p M (x 0 • v + η (x 0)))) := by
      simp only [hgdef, cutG, hΨφ, hNe]; rfl
    have hc : (A x + f (x, φ x)) 0 = -x 0 + w (nonlin P p M (x 0 • v + η (x 0))) := by
      rw [hfφ]; simp [hAdef, centreCoord_apply_zero]
    have hQP : specProj v w (P (p + (x 0 • v + η (x 0))) - p) =
        Ld (η (x 0)) + specProj v w (nonlin P p M (x 0 • v + η (x 0))) := by
      rw [hPe, map_add, specProj_apply (e := M _), hw, hLdef, deflate_apply, hwη, zero_smul,
        add_zero]
      simp only [map_add, map_smul, hv, hwv, hwη, smul_eq_mul, mul_one, add_zero]
      module
    have hwP' := hwP (x 0) (fun x => η (x 0)) x (hwη _)
    show -(orbitEmb m θ Ld (specProj v w (P (p + (x 0 • v + η (x 0))) - p) -
        η (w (P (p + (x 0 • v + η (x 0))) - p)))) =
      orbitEmb m θ Ld (η ((A x + f (x, φ x)) 0)) - B (orbitEmb m θ Ld (η (x 0))) - g (x, φ x)
    rw [hc, hBdef, orbitShift_orbitEmb hm hθ0.ne', hgφ, hQP, hwP']
    simp only [map_sub, map_add]
    abel
  -- the approximation of the centre manifold by the candidate
  have happrox := Map.CenterManifold.isBigO_sub_of_defect hAs hA hB hθ0.le hfl hgl hf0 hg0
    (by simpa using hεa) hh hh0 hinv hφ hφ0 hq hDc (by simpa using hκq) (by simpa using hκ1)
  set π₀ : (Fin m → ℝⁿ) →L[ℝ] ℝⁿ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n)) ⟨0, hm⟩
    with hπ₀
  have hy : (fun x : ℝ¹ => h x ⟨0, hm⟩ - η (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ q := by
    refine ((π₀.isBigO_comp _ _).trans happrox).congr_left fun x => ?_
    show (h x - orbitEmb m θ Ld (η (x 0))) ⟨0, hm⟩ = _
    rw [Pi.sub_apply, orbitEmb_zero]
  have heh : (fun x : ℝ¹ => x 0 • v + h x ⟨0, hm⟩) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    have := heη.add (hy.trans (isBigO_norm_pow_of_le hq))
    refine this.congr_left fun x => ?_
    abel
  have hevh : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + h x ⟨0, hm⟩‖ ≤ ρ₁ := by
    have := (heh.trans_tendsto hnorm0).eventually (Metric.closedBall_mem_nhds 0 hρ₁)
    filter_upwards [this] with x hx
    simpa using hx
  refine ⟨Map.CenterManifold.reducedMap A f h, fun x => h x ⟨0, hm⟩, hy, ?_,
    fun hr => localAsymptoticStable_of_translate
      (Map.CenterManifold.localAsymptoticStable_of_reduced hB hθ0.le hfl hgl hθ2 hh hh0 hinv
        (coordInv_coordMap hm θ) hρ₁ hG hr),
    fun hr => lyapunovStable_of_translate
      (Map.CenterManifold.lyapunovStable_of_reduced hAs hA hB hθ0.le hfl hgl
        (by simpa using hgap) hθ2 hh hh0 hinv (coordInv_coordMap hm θ) hρ₁ hG hr),
    fun hLS => Map.CenterManifold.lyapunovStable_reduced hh hh0 hinv hgraph hρ₁ hG
      (lyapunovStable_translate hLS)⟩
  filter_upwards [hevh] with x hxh
  have hΨh : coordInv v hm (x, h x) = x 0 • v + h x ⟨0, hm⟩ := by rw [coordInv_apply]
  have hfh : f (x, h x) = centreCoord w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
    simp only [hfdef, cutF, hΨh, hNcN _ hxh]; rfl
  rw [Map.CenterManifold.reducedMap, hfh]
  simp [hAdef, centreCoord_apply_zero]

/-! ## The expansion along the polynomial candidate, from the Taylor coefficients -/

/-- **The scalar map along the candidate.** If `P(p + e) = p + M e + P₂(e, e) + P₃(e³) + P₄(e⁴) +
P₅(e⁵) + O(‖e‖⁶)`, `w ∘ M = −w`, `w v = 1` and `w k₂ = w k₃ = w k₄ = 0`, then along
`t ↦ p + t v + t² k₂ + t³ k₃ + t⁴ k₄`
`w(P(p + t v + η(t)) − p) = −t + c₂ t² + c₃ t³ + c₄ t⁴ + c₅ t⁵ + O(t⁶)` with `c₂ = w P₂(v, v)`
and `cⱼ = w nⱼ` for the coefficients `nⱼ` of `curve_expansion`. -/
@[tmio T, powerlib_foundation] theorem scalar_expansion {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hwk₂ : w k₂ = 0) (hwk₃ : w k₃ = 0) (hwk₄ : w k₄ = 0) :
    (fun t : ℝ => w (P (p + (t • v + graphJet k₂ k₃ k₄ t)) - p) -
      (-t + w (P₂ v v) * t ^ 2 + w (curveCoeff₃ P₂ P₃ v k₂) * t ^ 3 +
        w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) * t ^ 4 +
        w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) * t ^ 5)) =O[𝓝 0] fun t => t ^ 6 := by
  have hC := curve_expansion (N := nonlin P p M) hρ₀ hTay v k₂ k₃ k₄
  refine ((w.isBigO_comp _ _).trans hC).congr_left fun t => ?_
  have hwe : w (t • v + graphJet k₂ k₃ k₄ t) = t := by
    simp [graphJet, map_add, map_smul, hwv, hwk₂, hwk₃, hwk₄]
  have hPe : P (p + (t • v + graphJet k₂ k₃ k₄ t)) - p =
      M (t • v + graphJet k₂ k₃ k₄ t) + nonlin P p M (t • v + graphJet k₂ k₃ k₄ t) := by
    simp only [nonlin]; abel
  show w (nonlin P p M (t • v + graphJet k₂ k₃ k₄ t) - _) = _
  rw [hPe, map_add, hw, hwe]
  simp only [map_sub, map_add, map_smul, smul_eq_mul]
  ring

/-- **The invariance defect of the polynomial candidate.** Under the fifth-order expansion of
`P` at `p` (`M v = −v`, `w ∘ M = −w`, `w v = 1`), let `k₂, k₃, k₄` solve the homological
equations of the flip
* `(I − M) k₂ = Q P₂(v, v)`,
* `(−I − M) k₃ = Q n₃ + 2 c₂ k₂`, `w k₃ = 0`,
* `(I − M) k₄ = Q n₄ − (c₂² − 2c₃) k₂ − 3c₂ k₃`,

with `Q e = e − (w e) v`, `c₂ = w P₂(v, v)`, `n₃ = curveCoeff₃`, `c₃ = w n₃`,
`n₄ = curveCoeff₄`. Then the candidate `η(t) = t² k₂ + t³ k₃ + t⁴ k₄` is invariant up to
`O(t⁵)`: `Q(P(p + t v + η(t)) − p) − η(w(P(p + t v + η(t)) − p)) = O(t⁵)`. The equations are
those of the coefficients of `t²`, `t³`, `t⁴`: `(λʲ − M) kⱼ = Q nⱼ − [tʲ](η(s(t)) − ...)` with
`λ = −1`, the right sides coming from the expansion `s(t) = −t + c₂ t² + c₃ t³ + O(t⁴)` of the
reduced coordinate in `η(s)`. -/
@[tmio T, powerlib_foundation] theorem defect_expansion_five {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hv : M v = -v) (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hk₃ : -k₃ - M k₃ = specProj v w (curveCoeff₃ P₂ P₃ v k₂) + (2 * w (P₂ v v)) • k₂)
    (hwk₃ : w k₃ = 0)
    (hk₄ : k₄ - M k₄ = specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) -
      (w (P₂ v v) ^ 2 - 2 * w (curveCoeff₃ P₂ P₃ v k₂)) • k₂ - (3 * w (P₂ v v)) • k₃) :
    (fun t : ℝ => specProj v w (P (p + (t • v + graphJet k₂ k₃ k₄ t)) - p) -
      graphJet k₂ k₃ k₄ (w (P (p + (t • v + graphJet k₂ k₃ k₄ t)) - p))) =O[𝓝 0]
      fun t => t ^ 5 := by
  have hwk₂ : w k₂ = 0 := by
    have := congrArg w hk₂
    rw [map_sub, hw, w_specProj hwv] at this
    linarith
  have hwk₄ : w k₄ = 0 := by
    have := congrArg w hk₄
    rw [map_sub, hw, map_sub, map_sub, w_specProj hwv, map_smul, map_smul, hwk₂, hwk₃] at this
    simp only [smul_eq_mul, mul_zero, sub_zero] at this
    linarith
  set c₂ := w (P₂ v v) with hc₂
  set c₃ := w (curveCoeff₃ P₂ P₃ v k₂) with hc₃
  set c₄ := w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) with hc₄
  set c₅ := w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) with hc₅
  -- the remainder of the map along the curve
  set ρ : ℝ → ℝⁿ := fun t => nonlin P p M (t • v + graphJet k₂ k₃ k₄ t) -
    (t ^ 2 • P₂ v v + t ^ 3 • curveCoeff₃ P₂ P₃ v k₂ + t ^ 4 • curveCoeff₄ P₂ P₃ P₄ v k₂ k₃ +
      t ^ 5 • curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) with hρ
  have hρO : ρ =O[𝓝 0] fun t => t ^ 6 := curve_expansion (N := nonlin P p M) hρ₀ hTay v k₂ k₃ k₄
  have hwe : ∀ t : ℝ, w (t • v + graphJet k₂ k₃ k₄ t) = t := fun t => by
    simp [graphJet, map_add, map_smul, hwv, hwk₂, hwk₃, hwk₄]
  have hPe : ∀ t : ℝ, P (p + (t • v + graphJet k₂ k₃ k₄ t)) - p =
      M (t • v + graphJet k₂ k₃ k₄ t) + (t ^ 2 • P₂ v v + t ^ 3 • curveCoeff₃ P₂ P₃ v k₂ +
        t ^ 4 • curveCoeff₄ P₂ P₃ P₄ v k₂ k₃ + t ^ 5 • curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄ +
        ρ t) := fun t => by
    simp only [hρ, nonlin]; abel
  -- the reduced coordinate `s(t) = −t + c₂ t² + c₃ t³ + σ(t)`, `σ = O(t⁴)`
  set σ : ℝ → ℝ := fun t => c₄ * t ^ 4 + c₅ * t ^ 5 + w (ρ t) with hσdef
  have hs : ∀ t : ℝ, w (P (p + (t • v + graphJet k₂ k₃ k₄ t)) - p) =
      -t + c₂ * t ^ 2 + c₃ * t ^ 3 + σ t := fun t => by
    rw [hPe, map_add, hw, hwe]
    simp only [hσdef, map_add, map_smul, smul_eq_mul]
    ring
  have hσ : σ =O[𝓝 0] fun t => t ^ 4 :=
    ((((isBigO_refl (fun t : ℝ => t ^ 4) _).const_mul_left c₄).add
      ((isBigO_pow_of_le (by norm_num : 4 ≤ 5)).const_mul_left c₅)).add
      ((w.isBigO_comp _ _).trans (hρO.trans (isBigO_pow_of_le (by norm_num)))))
  obtain ⟨S2, S3, S4⟩ := powers_expansion c₂ c₃ hσ
  -- the stable part of the map along the curve
  have hMk₂ : M k₂ = k₂ - specProj v w (P₂ v v) := by rw [← hk₂]; abel
  have hMk₃ : M k₃ = -k₃ - specProj v w (curveCoeff₃ P₂ P₃ v k₂) - (2 * c₂) • k₂ := by
    rw [← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at hk₃
    rw [← hk₃]; abel
  have hMk₄ : M k₄ = k₄ - specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) +
      (c₂ ^ 2 - 2 * c₃) • k₂ + (3 * c₂) • k₃ := by
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hk₄
    rw [← neg_eq_zero, ← hk₄]; abel
  have hQM : ∀ t : ℝ, specProj v w (M (t • v + graphJet k₂ k₃ k₄ t)) =
      t ^ 2 • M k₂ + t ^ 3 • M k₃ + t ^ 4 • M k₄ := fun t => by
    rw [specProj_apply, hw, hwe]
    simp only [graphJet, map_add, map_smul, hv]
    module
  have hsum := ((((isBigO_smul_const (isBigO_refl (fun t : ℝ => t ^ 5) _)
      (specProj v w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄))).add
      (((specProj v w).isBigO_comp _ _).trans (hρO.trans (isBigO_pow_of_le (by norm_num))))).sub
      (isBigO_smul_const S2 k₂)).sub (isBigO_smul_const S3 k₃)).sub (isBigO_smul_const S4 k₄)
  refine hsum.congr_left fun t => ?_
  rw [hs, hPe, map_add, hQM, hMk₂, hMk₃, hMk₄]
  simp only [graphJet, map_add, map_smul]
  module

/-! ## Solvability of the homological equations -/

/-- **The homological equations are uniquely solvable.** If a power of the deflated map
`L = M + v wᵀ` has norm below one (`w ∘ M = −w`, `w v = 1`), then for every `r` with `w r = 0`
the equation `(I − M) k = r` has exactly one solution, and `(−I − M) k = r` has exactly one
solution with `w k = 0`: `I − L` and `I + L` are injective (`L` has no eigenvalue `±1`), hence
onto, and `L = M` on `ker w`, which both equations preserve. In particular `k₂`, `k₃`, `k₄` of
`defect_expansion_five` exist and are unique, one after the other (the right sides lie in
`ker w`), so the coefficients `c₄`, `c₅` are determined by `P₂, …, P₅`, `v` and `w`. -/
@[tmio T, powerlib_foundation] theorem exists_homological
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ}
    (hLm : ‖deflate M v w ^ m‖ < 1) {r : ℝⁿ} (hr : w r = 0) :
    (∃! k : ℝⁿ, k - M k = r) ∧ (∃! k : ℝⁿ, w k = 0 ∧ -k - M k = r) := by
  set L := deflate M v w with hLdef
  have hfix : ∀ (s : ℝ) (k : ℝⁿ), L k = s • k → |s| = 1 → k = 0 := by
    intro s k hk hs
    have hpow : ∀ j : ℕ, (L ^ j) k = s ^ j • k := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ]
        show (L ^ j) (L k) = _
        rw [hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
    by_contra hk0
    have h1 : ‖k‖ ≤ ‖L ^ m‖ * ‖k‖ := by
      have := (L ^ m).le_opNorm k
      rwa [hpow, norm_smul, norm_pow, Real.norm_eq_abs, hs, one_pow, one_mul] at this
    have hpos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
    nlinarith
  have hLk : ∀ k : ℝⁿ, w k = 0 → L k = M k := fun k hk => by
    rw [hLdef, deflate_apply, hk, zero_smul, add_zero]
  have inj1 : Function.Injective
      ((ContinuousLinearMap.id ℝ ℝⁿ - L : ℝⁿ →L[ℝ] ℝⁿ) : ℝⁿ →ₗ[ℝ] ℝⁿ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have : k - L k = 0 := by simpa using hk
    exact hfix 1 k (by rw [one_smul]; exact (sub_eq_zero.mp this).symm) (by norm_num)
  have inj2 : Function.Injective
      ((ContinuousLinearMap.id ℝ ℝⁿ + L : ℝⁿ →L[ℝ] ℝⁿ) : ℝⁿ →ₗ[ℝ] ℝⁿ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have : k + L k = 0 := by simpa using hk
    exact hfix (-1) k (by rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_right this)
      (by norm_num)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := (LinearMap.injective_iff_surjective.mp inj1) r
    have hk' : k - L k = r := by simpa using hk
    have hwk : w k = 0 := by
      have := congrArg w hk'
      rwa [map_sub, w_deflate hw hwv, sub_zero, hr] at this
    refine ⟨k, by rwa [hLk k hwk] at hk', fun k' hk'' => ?_⟩
    have hd : (k' - k) - M (k' - k) = 0 := by
      rw [map_sub, ← hLk k hwk]
      have : k - L k = k' - M k' := by rw [hk', hk'']
      rw [← sub_eq_zero] at this
      calc k' - k - (M k' - L k) = -(k - L k - (k' - M k')) := by abel
        _ = 0 := by rw [this, neg_zero]
    have hwd : w (k' - k) = 0 := by
      have := congrArg w hd
      rw [map_sub, hw, map_zero] at this
      linarith
    have := hfix 1 (k' - k) (by
      rw [one_smul, hLk _ hwd]; exact (sub_eq_zero.mp hd).symm) (by norm_num)
    exact sub_eq_zero.mp this
  · obtain ⟨k, hk⟩ := (LinearMap.injective_iff_surjective.mp inj2) (-r)
    have hk' : k + L k = -r := by simpa using hk
    have hwk : w k = 0 := by
      have := congrArg w hk'
      rwa [map_add, w_deflate hw hwv, add_zero, map_neg, hr, neg_zero] at this
    rw [hLk k hwk] at hk'
    refine ⟨k, ⟨hwk, ?_⟩, fun k' ⟨hwk', hk''⟩ => ?_⟩
    · rw [← neg_neg r, ← hk']
      abel
    have hwd : w (k' - k) = 0 := by rw [map_sub, hwk, hwk', sub_zero]
    have hd : M (k' - k) = -(k' - k) := by
      have : -k' - M k' = -(k + M k) := by rw [hk'', hk', neg_neg]
      rw [map_sub]
      rw [← sub_eq_zero] at this ⊢
      rw [← neg_eq_zero, ← this]; abel
    have := hfix (-1) (k' - k) (by rw [neg_one_smul, hLk _ hwd, hd]) (by norm_num)
    exact sub_eq_zero.mp this

/-! ## The restricted map and the degenerate flip from the Taylor coefficients -/

/-- **The restricted map from the Taylor coefficients of `P`.** Let `P : ℝⁿ → ℝⁿ` fix `p` with
strict derivative `M`, `M v = −v`, `w ∘ M = −w`, `w v = 1`, a power of the deflated map
`M + v wᵀ` of norm below one, and the fifth-order expansion
`P(p + e) = p + M e + P₂(e, e) + P₃(e³) + P₄(e⁴) + P₅(e⁵) + O(‖e‖⁶)`; let `k₂, k₃, k₄` solve the
homological equations of `defect_expansion_five`. Then there is a map `r : ℝ¹ → ℝ¹` (the map
restricted to a centre manifold, in the coordinate `w`) with
`r(x) = −x + c₂ x² + c₃ x³ + c₄ x⁴ + c₅ x⁵ + O(x⁶)`,
`c₂ = w P₂(v, v)`, `c₃ = w n₃`, `c₄ = w n₄`, `c₅ = w n₅` (`curveCoeff₃`, `curveCoeff₄`,
`curveCoeff₅`), whose local asymptotic stability gives that of `P` at `p`, and which is Lyapunov
stable exactly when `P` is. `c₂` and `c₃` are the coefficients `a`, `b` of `exists_reduced_map`. -/
@[tmio T, powerlib_foundation] theorem exists_reduced_map_five {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflate M v w ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hk₃ : -k₃ - M k₃ = specProj v w (curveCoeff₃ P₂ P₃ v k₂) + (2 * w (P₂ v v)) • k₂)
    (hwk₃ : w k₃ = 0)
    (hk₄ : k₄ - M k₄ = specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) -
      (w (P₂ v v) ^ 2 - 2 * w (curveCoeff₃ P₂ P₃ v k₂)) • k₂ - (3 * w (P₂ v v)) • k₃) :
    ∃ r : ℝ¹ → ℝ¹, (∃ ρ K' : ℝ, 0 < ρ ∧ ∀ y : ℝ¹, ‖y‖ ≤ ρ →
        |r y 0 - (-y 0 + w (P₂ v v) * y 0 ^ 2 + w (curveCoeff₃ P₂ P₃ v k₂) * y 0 ^ 3 +
          w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) * y 0 ^ 4 +
          w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) * y 0 ^ 5)| ≤ K' * |y 0| ^ 6) ∧
      (Map.LocalAsymptoticStable r 0 → Map.LocalAsymptoticStable P p) ∧
      (Map.LyapunovStable r 0 ↔ Map.LyapunovStable P p) := by
  have hwk₂ : w k₂ = 0 := by
    have := congrArg w hk₂
    rw [map_sub, hw, w_specProj hwv] at this
    linarith
  have hwk₄ : w k₄ = 0 := by
    have := congrArg w hk₄
    rw [map_sub, hw, map_sub, map_sub, w_specProj hwv, map_smul, map_smul, hwk₂, hwk₃] at this
    simp only [smul_eq_mul, mul_zero, sub_zero] at this
    linarith
  -- the candidate
  have hη : HasStrictDerivAt (graphJet k₂ k₃ k₄) 0 0 := by
    have h := (((hasStrictDerivAt_pow 2 (0 : ℝ)).smul_const k₂).add
      ((hasStrictDerivAt_pow 3 (0 : ℝ)).smul_const k₃)).add
      ((hasStrictDerivAt_pow 4 (0 : ℝ)).smul_const k₄)
    have e : graphJet k₂ k₃ k₄ = fun t => t ^ 2 • k₂ + t ^ 3 • k₃ + t ^ 4 • k₄ := rfl
    rw [e]
    convert h using 1
    simp
  have hη0 : graphJet k₂ k₃ k₄ 0 = 0 := by simp [graphJet]
  have hwη : ∀ t, w (graphJet k₂ k₃ k₄ t) = 0 := fun t => by
    simp [graphJet, map_add, map_smul, hwk₂, hwk₃, hwk₄]
  have hD := defect_expansion_five hv hw hwv hρ₀ hTay hk₂ hk₃ hwk₃ hk₄
  obtain ⟨r, y, hy, hr, hLAS, hLS⟩ :=
    exists_reduced_map_near_candidate hP hPp hv hw hwv hm hLm hη hη0 hwη (by norm_num) hD
  -- the restricted map against the candidate's map
  have hx0 : Tendsto (fun x : ℝ¹ => x 0) (𝓝 0) (𝓝 0) := by
    have : Continuous fun x : ℝ¹ => x 0 := by fun_prop
    simpa using this.tendsto 0
  have hcurve : (fun t : ℝ => t • v + graphJet k₂ k₃ k₄ t) =O[𝓝 0] fun t => t ^ 1 := by
    have hid : (fun t : ℝ => t) =O[𝓝 0] fun t => t ^ 1 := by simpa using isBigO_refl _ _
    have hsc : ∀ (i : ℕ) (c : ℝⁿ), 1 ≤ i → (fun t : ℝ => t ^ i • c) =O[𝓝 0] fun t => t ^ 1 :=
      fun i c hi => isBigO_smul_const (isBigO_pow_of_le hi) c
    exact (isBigO_smul_const hid v).add (((hsc 2 k₂ (by norm_num)).add
      (hsc 3 k₃ (by norm_num))).add (hsc 4 k₄ (by norm_num)))
  have hβ : (fun x : ℝ¹ => x 0 • v + graphJet k₂ k₃ k₄ (x 0)) =O[𝓝 0] fun x => ‖x‖ :=
    ((hcurve.comp_tendsto hx0).trans (isBigO_coord_pow 1)).congr_right fun x => pow_one _
  have hαβ : (fun x : ℝ¹ => (x 0 • v + y x) - (x 0 • v + graphJet k₂ k₃ k₄ (x 0))) =O[𝓝 0]
      fun x => ‖x‖ ^ 5 := hy.congr_left fun x => by abel
  have hα : (fun x : ℝ¹ => x 0 • v + y x) =O[𝓝 0] fun x => ‖x‖ :=
    (hβ.add (hαβ.trans ((isBigO_norm_pow_of_le (by norm_num : 1 ≤ 5)).congr_right
      fun x => pow_one _))).congr_left fun x => by abel
  have hdiff := isBigO_sub_of_taylor_five (N := nonlin P p M) hρ₀ hTay
    (tendsto_norm_zero (E := ℝ¹)) hα hβ hαβ
  have hcand := (((w.isBigO_comp _ _).trans (curve_expansion (N := nonlin P p M) hρ₀ hTay v k₂
    k₃ k₄)).comp_tendsto hx0).trans (isBigO_coord_pow 6)
  have hrO : (fun x : ℝ¹ => r x 0 - (-x 0 + w (P₂ v v) * x 0 ^ 2 +
      w (curveCoeff₃ P₂ P₃ v k₂) * x 0 ^ 3 + w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) * x 0 ^ 4 +
      w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) * x 0 ^ 5)) =O[𝓝 0] fun x => ‖x‖ ^ 6 := by
    refine (((w.isBigO_comp _ _).trans hdiff).add hcand).congr' ?_ EventuallyEq.rfl
    filter_upwards [hr] with x hx
    rw [hx]
    simp only [Function.comp_apply, map_sub, map_add, map_smul, smul_eq_mul]
    ring
  -- the explicit bound
  obtain ⟨C, hC⟩ := hrO.bound
  obtain ⟨r₀, hr₀, hCb⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨r, ⟨r₀ / 2, C, half_pos hr₀, fun x hx => ?_⟩, hLAS, hLS⟩
  have := hCb (show dist x 0 < r₀ by rw [dist_zero_right]; linarith)
  rw [Real.norm_eq_abs, norm_pow, norm_norm, NormalForm.norm_state1] at this
  exact this

/-- **A degenerate flip decided by the Taylor coefficients of the map, stable side.** Under the
hypotheses of `exists_reduced_map_five`, if the flip coefficient vanishes,
`c₂² + c₃ = 0`, and `c₅ + 3c₂c₄ − 2c₂⁴ > 0` (`c₂ = w P₂(v, v)`, `c₃ = w n₃`, `c₄ = w n₄`,
`c₅ = w n₅`), the fixed point `p` of `P` is locally asymptotically stable, and not exponentially
stable (the multiplier `−1`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_degenerateFlip_taylor
    {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflate M v w ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hk₃ : -k₃ - M k₃ = specProj v w (curveCoeff₃ P₂ P₃ v k₂) + (2 * w (P₂ v v)) • k₂)
    (hwk₃ : w k₃ = 0)
    (hk₄ : k₄ - M k₄ = specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) -
      (w (P₂ v v) ^ 2 - 2 * w (curveCoeff₃ P₂ P₃ v k₂)) • k₂ - (3 * w (P₂ v v)) • k₃)
    (hdeg : w (P₂ v v) ^ 2 + w (curveCoeff₃ P₂ P₃ v k₂) = 0)
    (hκ : 0 < w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) +
      3 * w (P₂ v v) * w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) - 2 * w (P₂ v v) ^ 4) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨r, ⟨ρ, K', hρ, hb⟩, hS, -⟩ :=
    exists_reduced_map_five hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ hk₃ hwk₃ hk₄
  refine ⟨hS (Map.degenerateFlip_localAsymptoticStable hρ hdeg hκ hb).1, ?_⟩
  have hv0 : v ≠ 0 := by rintro rfl; simp at hwv
  exact Map.not_locallyExponentiallyStable_of_eigenvector hP.hasFDerivAt hPp hv0
    (μ := -1) (by rw [hv, neg_one_smul]) (by norm_num)

/-- **A degenerate flip decided by the Taylor coefficients of the map, unstable side.** Under the
hypotheses of `exists_reduced_map_five`, if `c₂² + c₃ = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ < 0`, the
fixed point `p` of `P` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_degenerateFlip_taylor {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflate M v w ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hk₃ : -k₃ - M k₃ = specProj v w (curveCoeff₃ P₂ P₃ v k₂) + (2 * w (P₂ v v)) • k₂)
    (hwk₃ : w k₃ = 0)
    (hk₄ : k₄ - M k₄ = specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) -
      (w (P₂ v v) ^ 2 - 2 * w (curveCoeff₃ P₂ P₃ v k₂)) • k₂ - (3 * w (P₂ v v)) • k₃)
    (hdeg : w (P₂ v v) ^ 2 + w (curveCoeff₃ P₂ P₃ v k₂) = 0)
    (hκ : w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) +
      3 * w (P₂ v v) * w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) - 2 * w (P₂ v v) ^ 4 < 0) :
    Map.Unstable P p := by
  obtain ⟨r, ⟨ρ, K', hρ, hb⟩, -, hLS⟩ :=
    exists_reduced_map_five hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ hk₃ hwk₃ hk₄
  exact fun hP' => Map.degenerateFlip_unstable hρ hdeg hκ hb (hLS.mpr hP')

/-- **Matrix form, stable side.** As `localAsymptoticStable_of_degenerateFlip_taylor`, with the
deflated monodromy given by a Schur stable matrix `Lm` (`Linear.op Lm = M + v wᵀ`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_degenerateFlip_taylor_matrix
    {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ} (hL : Linear.op Lm = deflate M v w)
    (hS : LTI.SchurStable Lm) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hk₃ : -k₃ - M k₃ = specProj v w (curveCoeff₃ P₂ P₃ v k₂) + (2 * w (P₂ v v)) • k₂)
    (hwk₃ : w k₃ = 0)
    (hk₄ : k₄ - M k₄ = specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) -
      (w (P₂ v v) ^ 2 - 2 * w (curveCoeff₃ P₂ P₃ v k₂)) • k₂ - (3 * w (P₂ v v)) • k₃)
    (hdeg : w (P₂ v v) ^ 2 + w (curveCoeff₃ P₂ P₃ v k₂) = 0)
    (hκ : 0 < w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) +
      3 * w (P₂ v v) * w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) - 2 * w (P₂ v v) ^ 4) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact localAsymptoticStable_of_degenerateFlip_taylor hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ hk₃
    hwk₃ hk₄ hdeg hκ

/-- **Matrix form, unstable side.** As `unstable_of_degenerateFlip_taylor`, with the deflated
monodromy given by a Schur stable matrix `Lm`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_degenerateFlip_taylor_matrix {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ} (hL : Linear.op Lm = deflate M v w)
    (hS : LTI.SchurStable Lm) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ K * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hk₃ : -k₃ - M k₃ = specProj v w (curveCoeff₃ P₂ P₃ v k₂) + (2 * w (P₂ v v)) • k₂)
    (hwk₃ : w k₃ = 0)
    (hk₄ : k₄ - M k₄ = specProj v w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) -
      (w (P₂ v v) ^ 2 - 2 * w (curveCoeff₃ P₂ P₃ v k₂)) • k₂ - (3 * w (P₂ v v)) • k₃)
    (hdeg : w (P₂ v v) ^ 2 + w (curveCoeff₃ P₂ P₃ v k₂) = 0)
    (hκ : w (curveCoeff₅ P₂ P₃ P₄ P₅ v k₂ k₃ k₄) +
      3 * w (P₂ v v) * w (curveCoeff₄ P₂ P₃ P₄ v k₂ k₃) - 2 * w (P₂ v v) ^ 4 < 0) :
    Map.Unstable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact unstable_of_degenerateFlip_taylor hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ hk₃ hwk₃ hk₄
    hdeg hκ

end Reduction

end powerlib.Periodic.FlipReduction
