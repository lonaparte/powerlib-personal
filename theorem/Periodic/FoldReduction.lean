import theorem.Periodic.DegenerateFlipReduction

/-! # A fixed point with a simple multiplier `+1`: reduction to the fold and cubic normal forms

At a periodic solution `x_*` of a `T`-periodic, non-autonomous system `ẋ = G(t, x)` (a forced or
pumped system) whose monodromy has the simple multiplier `+1`, the linearization does not decide
stability (`Periodic.critical_plus_undecided`); the period map `P`, `P(x_*(0)) = x_*(0)`, does.
When every other multiplier lies strictly inside the unit circle, `P` has a one-dimensional centre
manifold, and the map restricted to it is `r(x) = x + a x² + b x³ + O(x⁴)` with the **fold
coefficient** `a = w P₂(v, v)` and the **cubic coefficient**
`b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))`, `(I − M) k₂ = Q P₂(v, v)`, where
`P(p + e) = p + M e + P₂(e, e) + P₃(e, e, e) + O(‖e‖⁴)`, `M v = v`, `wᵀ M = wᵀ`, `w v = 1` and
`Q e = e − (w e) v`. The decisions (fold / transcritical type and pitchfork type):
`a ≠ 0` — unstable; `a = 0`, `b < 0` — locally asymptotically, never exponentially, stable;
`a = 0`, `b > 0` — unstable. With `B = D²P(p) = 2P₂` and `C = D³P(p) = 6P₃` these are
Kuznetsov's `(1/2)⟨w, B(v, v)⟩` and, at `a = 0`,
`(1/6)⟨w, C(v, v, v)⟩ + (1/2)⟨w, B(v, k)⟩`, `(I − M) k = B(v, v)`. At `a = 0` the cubic coefficient
does not depend on the solution `k₂`, which is determined up to a multiple of `v`
(`cubicCoeff_add_smul`, `eq_smul_of_apply_eq`).

The machinery of `theorem/Periodic/FlipReduction.lean` (the multiplier `−1`) is reused, not
duplicated, through one observation: the **reflected monodromy** `M_μ = M − (1 + μ) v wᵀ` moves a
simple multiplier `μ` at `v` to `−1` and keeps `M` on `ker w`, its deflation `M_μ + v wᵀ` is the
deflation `M − μ v wᵀ` at `μ`, and the map `P_μ(y) = P(y) − (1 + μ) w(y − p) v` has the derivative
`M_μ` and the same nonlinearity as `P`. So the adapted norm, the coordinates `Φ`, `Ψ`, the cut-off
nonlinearities and their conjugacy (`FlipReduction.coordMap_conj` for `P_μ`) serve every
`μ = ±1`; the linear part `−1` of `P_μ` becomes `μ` for `P` (`coordMap_conj_at`). The invariance
defect at `μ` is `FlipReduction.defect_expansion` read along `−μ v` and the isometry `x ↦ −μ x`
(`defect_expansion_at`), and the expansion of the reduced map is `FlipReduction.reduced_expansion`
itself. The centre manifold, the reduction principle, the asymptotic phase and the approximation
theorem with `q = 3` (`theorem/Map/CenterManifold.lean`, `theorem/Map/CenterReduction.lean`,
`theorem/Map/AsymptoticPhase.lean`) give the reduced map for
`|μ| = 1` (`exists_reduced_map_at`), and the scalar normal forms of
`theorem/Periodic/CriticalMultiplier.lean` (`Map.quadratic_unstable`,
`Map.cubic_localAsymptoticStable`, `Map.cubic_unstable`) decide it at `μ = +1`.

Near `p` every fixed point of `P` lies on the centre manifold, and the reduced map fixes its centre
coordinate. Hence fixed points accumulating at `p` force `a = b = 0`
(`foldCoeffs_eq_zero_of_fixedPoints`), and a curve of fixed points transverse to `ker w` makes the
reduced map the identity: `p` is Lyapunov stable, not asymptotically stable
(`lyapunovStable_of_fixedCurve`). For the period map of a periodic orbit of an **autonomous**
system the orbit itself is such a curve and the multiplier `+1` is the trivial one: the fold and
pitchfork verdicts never apply (`theorem/Periodic/FoldOrbit.lean`).

Scope.
* The map semantics on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`Map.LocalAsymptoticStable`,
  `Map.Unstable`, `Map.LocallyExponentiallyStable`) for a map `P : ℝⁿ → ℝⁿ` with a fixed point
  `p`. For a periodic solution, `P` is the period map and `p = x_*(0)`; its regularity is a
  **hypothesis** here (strict derivative `M` at `p`, cubic Taylor expansion with remainder
  `K ‖e‖⁴` on `‖e‖ ≤ ρ₀`), derived from a `C⁴` field in `theorem/Periodic/FoldOrbit.lean`.
* The spectral hypothesis is in projector form: `M v = v`, `w ∘ M = w`, `w v = 1`, and a power of
  the deflated map `L = M − v wᵀ` of norm below one. `multipliers_of_deflateAt` (for every real
  multiplier `|μ| ≥ 1`) shows what it says: every complex multiplier other than `μ` lies strictly
  inside the unit circle, every eigenvector of `μ` is a multiple of `v`, and there is no Jordan
  chain at `μ`. The matrix forms (`Linear.op Lm = M − v wᵀ`, `LTI.SchurStable Lm`) are the
  `_matrix` theorems.
* `P₂` is a continuous bilinear map (not assumed symmetric) and `P₃` a continuous trilinear map
  on the diagonal (`ContinuousMultilinearMap` on `Fin 3`), as in `FlipReduction`. In
  `exists_reduced_map_at` `k₂` solves the deflated equation `k₂ − L k₂ = Q P₂(v, v)` (unique,
  `exists_sub_apply_eq`, and then `w k₂ = 0`); the decision theorems accept any solution of
  `(I − M) k₂ = Q P₂(v, v)`.
* `a = b = 0` is not decided (the quartic and higher coefficients are needed; no finite order
  suffices in general). Degenerate cases are not treated; nor are the multipliers `−1` (done in
  `FlipReduction`, which `exists_reduced_map_at` also covers at `μ = −1`) or complex pairs.
* Generic; nothing here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), Ch. 4 (the fold of fixed
points of maps, the normal form `η ↦ η + a η² + …`), Ch. 9 (the cusp point of a map, where the
fold coefficient vanishes and the cubic normal form `η ↦ η + c η³` decides) and §5.4 (restricted
normalized maps by the projection method: `(1/2)⟨w, B(v, v)⟩` and
`(1/6)(⟨w, C(v, v, v)⟩ + 3⟨w, B(v, k)⟩)`); Carr, *Applications of Centre Manifold Theory* (1981),
Ch. 2; Iooss, *Bifurcation of Maps and Applications* (1979); the open items of
`theorem/Periodic/CriticalMultiplier.lean` (Scope: "The multiplier `+1` of a nonconstant orbit is
not reduced") and `theorem/Periodic/FlipOrbit.lean` (Scope: "A nonconstant orbit with the
multiplier `+1` … needs the centre-manifold reduction at `+1`, which `FlipReduction` does not
provide").

Results.
* The splitting at `μ`: `deflateAt` (`L = M − μ v wᵀ`), `reflect` (`M_μ = M − (1 + μ) v wᵀ`),
  `deflateAt_apply`, `reflect_apply`, `deflateAt_neg_one` (at `−1` it is
  `FlipReduction.deflate`), `deflate_reflect` (`M_μ + v wᵀ = L`), `reflect_self` (`M_μ v = −v`),
  `w_reflect` (`w ∘ M_μ = −w`), `w_deflateAt` (`w ∘ L = 0`).
* `coordMap_conj_at` — the map in the coordinates of `M_μ`: linear part `(μ, B̂)`.
* `defect_expansion_at` — the invariance defect of `x ↦ x² k₂` is `O(‖x‖³)` at `|μ| = 1`.
* Linear algebra: `eq_zero_of_apply_eq_smul` (no eigenvector of a unimodular eigenvalue when
  `‖Lᵐ‖ < 1`), `exists_sub_apply_eq` (the homological equation `k − L k = y` is solvable),
  `eq_smul_of_apply_eq` (`μ` geometrically simple), `multipliers_of_deflateAt`.
* **The reduction** `exists_reduced_map_at` (`|μ| = 1`): a scalar map
  `r(x) = μ x + a x² + b x³ + O(x⁴)` whose asymptotic stability gives that of `P`, which is
  Lyapunov stable exactly when `P` is, and which fixes the centre coordinate of every fixed point
  of `P` near `p`.
* At `+1`: `cubicCoeff_add_smul` (`b(k₂ + c v) = b(k₂) + 2 c a`), `specProj_sub_deflateAt`;
  **the theorems** `unstable_of_foldCoeff_ne_zero` (`a ≠ 0`: unstable),
  `localAsymptoticStable_of_cubicCoeff_neg` (`a = 0`, `b < 0`: locally asymptotically, not
  exponentially, stable), `unstable_of_cubicCoeff_pos` (`a = 0`, `b > 0`: unstable), and their
  matrix forms `unstable_of_foldCoeff_ne_zero_matrix`,
  `localAsymptoticStable_of_cubicCoeff_neg_matrix`, `unstable_of_cubicCoeff_pos_matrix`.
* `not_localAsymptoticStable_of_fixedPoints` (fixed points accumulating at `p` exclude local
  asymptotic stability), `foldCoeffs_eq_zero_of_fixedPoints` — they force `a = 0`, `b = 0`;
  `lyapunovStable_of_fixedCurve` — a curve of fixed points transverse to `ker w` makes `p`
  Lyapunov stable, not asymptotically stable (the reduced map is the identity).

Corrections.
None: an extension (the critical multiplier `+1` of a periodic solution of a non-autonomous
system with a stable complement, decided beyond the linearization). `FlipReduction`'s
`exists_reduced_map` is the case `μ = −1` of `exists_reduced_map_at` (with the deflated form of
the homological equation, equivalent at `−1`).

Family and connection conclusions.
None: static evidence on maps (the period map of a periodic orbit).
-/

noncomputable section

open Filter Topology Asymptotics

namespace powerlib.Periodic.FoldReduction

open FlipReduction

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-! ## The splitting along a simple multiplier `μ` -/

/-- The deflated monodromy at a simple multiplier `μ`: `L = M − μ v wᵀ`, equal to `M` on `ker w`
and to `0` on the eigenvector `v`. -/
def deflateAt (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) (μ : ℝ) : ℝⁿ →L[ℝ] ℝⁿ :=
  M - μ • w.smulRight v

/-- The monodromy with its multiplier `μ` at `v` moved to `−1`: `M_μ = M − (1 + μ) v wᵀ`. It
equals `M` on `ker w`, so the coordinates of `FlipReduction` built on `M_μ` split `M`. -/
def reflect (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) (μ : ℝ) : ℝⁿ →L[ℝ] ℝⁿ :=
  M - (1 + μ) • w.smulRight v

@[tmio T, powerlib_foundation] theorem deflateAt_apply (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ)
    (w : ℝⁿ →L[ℝ] ℝ) (μ : ℝ) (e : ℝⁿ) : deflateAt M v w μ e = M e - (μ * w e) • v := by
  simp [deflateAt, mul_smul]

@[tmio T, powerlib_foundation] theorem reflect_apply (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ)
    (w : ℝⁿ →L[ℝ] ℝ) (μ : ℝ) (e : ℝⁿ) : reflect M v w μ e = M e - ((1 + μ) * w e) • v := by
  simp [reflect, mul_smul]

/-- At `μ = −1` the deflation is `FlipReduction.deflate`. -/
@[tmio T, powerlib_foundation] theorem deflateAt_neg_one (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ)
    (w : ℝⁿ →L[ℝ] ℝ) : deflateAt M v w (-1) = deflate M v w := by
  ext1 e
  rw [deflateAt_apply, deflate_apply]
  module

/-- The deflation of the reflected monodromy is the deflation at `μ`: `M_μ + v wᵀ = M − μ v wᵀ`. -/
@[tmio T, powerlib_foundation] theorem deflate_reflect (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ)
    (w : ℝⁿ →L[ℝ] ℝ) (μ : ℝ) : deflate (reflect M v w μ) v w = deflateAt M v w μ := by
  ext1 e
  rw [deflate_apply, reflect_apply, deflateAt_apply]
  module

variable {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {v : EuclideanSpace ℝ (Fin n)} {w : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {μ : ℝ}

@[tmio T, powerlib_foundation] theorem reflect_self (hv : M v = μ • v) (hwv : w v = 1) :
    reflect M v w μ v = -v := by
  rw [reflect_apply, hv, hwv, mul_one]
  module

@[tmio T, powerlib_foundation] theorem w_reflect (hw : ∀ e, w (M e) = μ * w e) (hwv : w v = 1)
    (e : ℝⁿ) : w (reflect M v w μ e) = -w e := by
  rw [reflect_apply, map_sub, map_smul, hw, hwv, smul_eq_mul]
  ring

@[tmio T, powerlib_foundation] theorem w_deflateAt (hw : ∀ e, w (M e) = μ * w e)
    (hwv : w v = 1) (e : ℝⁿ) : w (deflateAt M v w μ e) = 0 := by
  rw [deflateAt_apply, map_sub, map_smul, hw, hwv, smul_eq_mul]
  ring

/-- **The map in the coordinates at a multiplier `μ`.** With the coordinates
`Φ = coordMap M_μ v w m θ` of `FlipReduction` built on the reflected monodromy `M_μ`, where the
cut-off `Ñ` equals the nonlinearity `N e = P(p + e) − p − M e`, the map `G e = P(p + e) − p` is
read as the split map with linear part `(μ, B̂)` and the nonlinearities `cutF`, `cutG` of `M_μ`;
`B̂` is the weighted shift of the deflation `M_μ + v wᵀ = M − μ v wᵀ`. It is
`FlipReduction.coordMap_conj` for `P_μ(y) = P(y) − (1 + μ) w(y − p) v`. -/
@[tmio T, powerlib_foundation] theorem coordMap_conj_at {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hv : M v = μ • v) (hw : ∀ e, w (M e) = μ * w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ : θ ≠ 0) {Nc : ℝⁿ → ℝⁿ} {e : ℝⁿ} (he : Nc e = nonlin P p M e) :
    coordMap (reflect M v w μ) v w m θ (P (p + e) - p) =
      Map.CenterManifold.splitMap (μ • ContinuousLinearMap.id ℝ ℝ¹)
        (orbitShift m hm θ (deflate (reflect M v w μ) v w))
        (cutF (reflect M v w μ) v w hm θ Nc) (cutG (reflect M v w μ) v w hm θ Nc)
        (coordMap (reflect M v w μ) v w m θ e) := by
  set P' : ℝⁿ → ℝⁿ := fun y => P y - ((1 + μ) * w (y - p)) • v with hP'
  have he' : Nc e = nonlin P' p (reflect M v w μ) e := by
    rw [he]
    simp only [nonlin, hP', reflect_apply, add_sub_cancel_left]
    abel
  have h := coordMap_conj (P := P') (reflect_self hv hwv) (w_reflect hw hwv) hwv hm hθ he'
  have hP : P (p + e) - p = (P' (p + e) - p) + ((1 + μ) * w e) • v := by
    simp only [hP', add_sub_cancel_left]
    abel
  have hΦv : coordMap (reflect M v w μ) v w m θ v = (EuclideanSpace.single 0 1, 0) := by
    simp only [coordMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, specProj_self hwv, map_zero]
    simp [centreCoord, hwv]
  have hΦ1 : (coordMap (reflect M v w μ) v w m θ e).1 = w e • EuclideanSpace.single 0 1 := by
    simp [coordMap, centreCoord]
  rw [hP, map_add, h, map_smul, hΦv]
  simp only [Map.CenterManifold.splitMap]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_mk, neg_apply, ContinuousLinearMap.id_apply, smul_apply,
      hΦ1]
    module
  · simp

/-! ## The invariance defect at a multiplier `μ = ±1` -/

/-- **The invariance defect of the quadratic candidate at `μ = ±1`.** With `e(x) = (x 0) v +
(x 0)² k₂` and `k₂ − L k₂ = Q (P₂ v v)`, the stable defect
`(μ x₀ + w N(e))² k₂ − x₀² L k₂ − Q N(e)` of the candidate graph `x ↦ (x 0)² k₂` is `O(‖x‖³)`
for `|μ| = 1`. It is `FlipReduction.defect_expansion` (the case `μ = −1`) read along `−μ v` and
the isometry `x ↦ −μ x` of `ℝ¹`. -/
@[tmio T, powerlib_foundation] theorem defect_expansion_at {N : ℝⁿ → ℝⁿ}
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (w : ℝⁿ →L[ℝ] ℝ) (v k₂ : ℝⁿ) (L Q : ℝⁿ →L[ℝ] ℝⁿ) {μ : ℝ} (hμ : |μ| = 1)
    (hk : k₂ - L k₂ = Q (P₂ v v)) :
    (fun x : ℝ¹ => (μ * x 0 + w (N (x 0 • v + x 0 ^ 2 • k₂))) ^ 2 • k₂ - x 0 ^ 2 • L k₂ -
      Q (N (x 0 • v + x 0 ^ 2 • k₂))) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
  have hμ2 : μ ^ 2 = 1 := by rw [← sq_abs, hμ, one_pow]
  have hk' : k₂ - L k₂ = Q (P₂ ((-μ) • v) ((-μ) • v)) := by
    rw [hk]
    simp only [map_smul, smul_apply, smul_smul, ← sq, neg_sq, hμ2, one_smul]
  have h := defect_expansion hρ₀ hTay w ((-μ) • v) k₂ L Q hk'
  set s : ℝ¹ →L[ℝ] ℝ¹ := (-μ) • ContinuousLinearMap.id ℝ ℝ¹ with hs
  have hs0 : Tendsto s (𝓝 0) (𝓝 0) := by simpa using s.continuous.tendsto 0
  have hsn : ∀ x, ‖s x‖ = ‖x‖ := fun x => by
    rw [hs, smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs, abs_neg, hμ,
      one_mul]
  refine ((h.comp_tendsto hs0).trans (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)))
    |>.congr_left fun x => ?_
  · simp only [Function.comp_apply, norm_pow, norm_norm, hsn, one_mul, le_refl]
  · have e1 : s x 0 = -μ * x 0 := by
      simp [hs]
    have e2 : (-μ * x 0) • ((-μ) • v) = x 0 • v := by
      rw [smul_smul]; congr 1; linear_combination x 0 * hμ2
    have e3 : (-μ * x 0) ^ 2 = x 0 ^ 2 := by linear_combination x 0 ^ 2 * hμ2
    simp only [Function.comp_apply]
    rw [e1, e2, e3, neg_mul, neg_neg]

/-! ## The reduction of a fixed point with a simple multiplier `μ = ±1` -/

/-- A map with a power of norm below one has no eigenvector of an eigenvalue `|μ| = 1`:
`‖z‖ = ‖Lᵐ z‖ ≤ ‖Lᵐ‖ ‖z‖`. -/
@[tmio T, powerlib_foundation] theorem eq_zero_of_apply_eq_smul {m : ℕ} {L : ℝⁿ →L[ℝ] ℝⁿ}
    (hLm : ‖L ^ m‖ < 1) (hμ : |μ| = 1) {z : ℝⁿ} (hz : L z = μ • z) : z = 0 := by
  have hpow : ∀ j : ℕ, (L ^ j) z = μ ^ j • z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hz, map_smul,
        ih, smul_smul, pow_succ, mul_comm]
  have h1 : ‖z‖ ≤ ‖L ^ m‖ * ‖z‖ := by
    calc ‖z‖ = ‖(L ^ m) z‖ := by
          rw [hpow m, norm_smul, norm_pow, Real.norm_eq_abs, hμ, one_pow, one_mul]
      _ ≤ ‖L ^ m‖ * ‖z‖ := (L ^ m).le_opNorm z
  have h2 : ‖z‖ ≤ 0 := by nlinarith [norm_nonneg z]
  exact norm_le_zero_iff.mp h2

/-- `I − L` is onto when a power of `L` has norm below one (`eq_zero_of_apply_eq_smul`: it is
one-to-one, and `ℝⁿ` is finite-dimensional). So the homological equation `k − L k = y` has a
solution, unique, for every `y`. -/
@[tmio T, powerlib_foundation] theorem exists_sub_apply_eq {m : ℕ} {L : ℝⁿ →L[ℝ] ℝⁿ}
    (hLm : ‖L ^ m‖ < 1) (y : ℝⁿ) : ∃ k, k - L k = y := by
  set S : ℝⁿ →ₗ[ℝ] ℝⁿ := (LinearMap.id - (L : ℝⁿ →ₗ[ℝ] ℝⁿ)) with hS
  have hinj : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have : z - L z = 0 := by simpa [hS] using hz
    exact eq_zero_of_apply_eq_smul hLm (μ := 1) (by simp) (by
      rw [one_smul]; exact (sub_eq_zero.mp this).symm)
  obtain ⟨k, hk⟩ := (LinearMap.injective_iff_surjective.mp hinj) y
  exact ⟨k, by simpa [hS] using hk⟩

/-- **The multiplier `μ` is geometrically simple.** Under the projector hypothesis (`M v = μ v`,
`w ∘ M = μ w`, `w v = 1`, `|μ| = 1`, a power of `M − μ v wᵀ` of norm below one), every
eigenvector of `μ` is a multiple of `v`: `M z = μ z ⇒ z = (w z) v`. -/
@[tmio T, powerlib_foundation] theorem eq_smul_of_apply_eq (hμ : |μ| = 1) (hv : M v = μ • v)
    (hwv : w v = 1) {m : ℕ} (hLm : ‖deflateAt M v w μ ^ m‖ < 1) {z : ℝⁿ}
    (hz : M z = μ • z) : z = w z • v := by
  have h0 : deflateAt M v w μ (z - w z • v) = μ • (z - w z • v) := by
    rw [deflateAt_apply, map_sub, map_smul, map_sub, map_smul, hz, hv, hwv, smul_eq_mul,
      mul_one, sub_self, mul_zero, zero_smul, sub_zero]
    module
  exact sub_eq_zero.mp (eq_zero_of_apply_eq_smul hLm hμ h0)

/-- **The reduced map of a fixed point with a simple multiplier `μ = ±1`.** Let `P : ℝⁿ → ℝⁿ`
fix `p` with strict derivative `M` there, `M v = μ v`, `w ∘ M = μ w`, `w v = 1`, `|μ| = 1`, the
deflated map `L = M − μ v wᵀ` with some power of norm below one (every other multiplier strictly
inside the unit circle), and the cubic Taylor expansion
`P(p + e) = p + M e + P₂ e e + P₃(e, e, e) + O(‖e‖⁴)`; let `k₂ − L k₂ = Q P₂(v, v)` with the
spectral projection `Q e = e − (w e) v` (so `w k₂ = 0` and `(I − M) k₂ = Q P₂(v, v)`). Then there
is a map `r : ℝ¹ → ℝ¹` (the map restricted to a centre manifold, in the coordinate `w`) with
`r(x) = μ x + a x² + b x³ + O(x⁴)`, `a = w P₂(v, v)`,
`b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))`, whose local asymptotic stability gives that of
`P` at `p` and which is Lyapunov stable exactly when `P` is (the asymptotic phase,
`Map.CenterManifold.lyapunovStable_iff`); and near `p` every fixed point `p + e` of `P`
lies on the centre manifold: its coordinate `w e` is a fixed point of `r`, and it is `p` when
`w e = 0`. -/
@[tmio T, powerlib_foundation] theorem exists_reduced_map_at {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hμ : |μ| = 1) (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = μ • v)
    (hw : ∀ e, w (M e) = μ * w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflateAt M v w μ ^ m‖ < 1) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - deflateAt M v w μ k₂ = specProj v w (P₂ v v)) :
    ∃ r : ℝ¹ → ℝ¹, (∃ ρ K' : ℝ, 0 < ρ ∧ ∀ y : ℝ¹, ‖y‖ ≤ ρ →
        |r y 0 - (μ * y 0 + w (P₂ v v) * y 0 ^ 2 +
          (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) * y 0 ^ 3)| ≤ K' * |y 0| ^ 4) ∧
      (Map.LocalAsymptoticStable r 0 → Map.LocalAsymptoticStable P p) ∧
      (Map.LyapunovStable r 0 ↔ Map.LyapunovStable P p) ∧
      ∃ ρ' > 0, ∀ e, ‖e‖ < ρ' → P (p + e) = p + e →
        r (centreCoord w e) = centreCoord w e ∧ (w e = 0 → e = 0) := by
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ
  -- the spectral data, in the reflected monodromy `M' = M − (1 + μ) v wᵀ`
  have hv' : reflect M v w μ v = -v := reflect_self hv hwv
  have hw' : ∀ e, w (reflect M v w μ e) = -w e := w_reflect hw hwv
  rw [← deflate_reflect] at hLm hk₂
  set L := deflate (reflect M v w μ) v w with hLdef
  have hLk : k₂ - L k₂ = specProj v w (P₂ v v) := hk₂
  obtain ⟨θ, hθ0, hθ1, hθm⟩ := exists_rate hm hLm
  -- the size of the nonlinearities
  have hεr : 0 < (1 - θ) / 8 := by linarith
  let ε : NNReal := ⟨(1 - θ) / 8, hεr.le⟩
  have hεe : (ε : ℝ) = (1 - θ) / 8 := rfl
  have hε0 : 0 < ε := by rw [← NNReal.coe_pos, hεe]; exact hεr
  have hgap : θ + 3 * ε < 1 := by rw [hεe]; linarith
  have hθ2 : θ + 2 * ε < 1 := by rw [hεe]; linarith
  have hεa : (ε : ℝ) < 1 := by rw [hεe]; linarith
  have hκ1 : θ + ε < 1 - ε := by rw [hεe]; linarith
  have hκq : θ + ε < (1 - ε) ^ 3 := by
    have h1 : 1 - 3 * (ε : ℝ) ≤ (1 - ε) ^ 3 := by
      have := ε.coe_nonneg
      nlinarith [sq_nonneg (ε : ℝ), mul_nonneg (sq_nonneg (ε : ℝ)) (by linarith : (0 : ℝ) ≤ 3 - ε)]
    rw [hεe] at h1 ⊢; linarith
  -- coordinates and the linear part
  set Φ := coordMap (reflect M v w μ) v w m θ with hΦ
  set Ψ := coordInv (n := n) v hm with hΨ
  set B := orbitShift m hm θ L with hBdef
  set A : ℝ¹ →L[ℝ] ℝ¹ := μ • ContinuousLinearMap.id ℝ ℝ¹ with hAdef
  have hAs : Function.Surjective A := fun x => ⟨μ⁻¹ • x, by
    rw [hAdef, smul_apply, ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hμ0,
      one_smul]⟩
  have hA : ∀ x, 1 * ‖x‖ ≤ ‖A x‖ := fun x => by
    rw [hAdef, smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs, hμ]
  have hB : ∀ u, ‖B u‖ ≤ θ * ‖u‖ := norm_orbitShift_le hm hθ0 hθm
  -- the cut-off nonlinearity
  obtain ⟨hN, hN0⟩ := nonlin_spec hP hPp
  set ε' : NNReal := ε / ((‖Φ‖₊ + 1) * (‖Ψ‖₊ + 1)) with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨ρ₁, hρ₁, Nc, hNcl, hNc0, hNcN⟩ :=
    Map.CenterManifold.exists_lipschitz_cutoff hN hN0 hε'0
  set f := cutF (reflect M v w μ) v w hm θ Nc with hfdef
  set g := cutG (reflect M v w μ) v w hm θ Nc with hgdef
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
  set T : ℝⁿ →L[ℝ] (Fin m → ℝⁿ) := (orbitEmb m θ L).comp (specProj v w) with hTdef
  set Kr : Submodule ℝ (Fin m → ℝⁿ) := LinearMap.range (T : ℝⁿ →ₗ[ℝ] (Fin m → ℝⁿ)) with hKr
  have hKc : IsClosed (Kr : Set (Fin m → ℝⁿ)) := Submodule.closed_of_finiteDimensional _
  have hBK : ∀ y ∈ Kr, B y ∈ Kr := by
    rintro _ ⟨z, rfl⟩
    refine ⟨reflect M v w μ z, ?_⟩
    simp only [hTdef, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply, hBdef]
    rw [orbitShift_orbitEmb hm hθ0.ne', (deflate_specProj hv' hw' hwv z).1]
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
    fun e he => coordMap_conj_at hv hw hwv hm hθ0.ne' (hNcN e he.le)
  have hTay' : ∀ e, ‖e‖ ≤ ρ₀ →
      ‖nonlin P p M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4 := hTay
  -- the approximation of the centre manifold by `x ↦ (x 0)² k₂`
  set φ : ℝ¹ → (Fin m → ℝⁿ) := fun x => orbitEmb m θ L (x 0 ^ 2 • k₂) with hφdef
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  have hφ : HasStrictFDerivAt φ (0 : ℝ¹ →L[ℝ] (Fin m → ℝⁿ)) 0 := by
    have h1 : HasStrictFDerivAt (fun x : ℝ¹ => x 0)
        (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) 0 := by
      have e : (fun x : ℝ¹ => x 0) = ⇑(EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) := by
        funext x; simp
      rw [e]
      exact ContinuousLinearMap.hasStrictFDerivAt
        (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ)
    have h2 := ((h1.pow 2).smul_const k₂)
    have h3 := (orbitEmb m θ L).hasStrictFDerivAt.comp (0 : ℝ¹) h2
    convert h3 using 1
    ext x
    simp
  have hu1' : (fun x : ℝ¹ => x 0) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    simpa using isBigO_coord_pow 1
  have he₂ : (fun x : ℝ¹ => x 0 • v + x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 1 :=
    (isBigO_smul_const hu1' v).add ((isBigO_smul_const (isBigO_coord_pow 2) k₂).trans
      (isBigO_norm_pow_of_le (by norm_num)))
  have hnorm0 : Tendsto (fun x : ℝ¹ => ‖x‖ ^ 1) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_norm_zero (E := ℝ¹)).pow 1
  have hev₂ : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + x 0 ^ 2 • k₂‖ ≤ ρ₁ := by
    have := (he₂.trans_tendsto hnorm0).eventually (Metric.closedBall_mem_nhds 0 hρ₁)
    filter_upwards [this] with x hx
    simpa using hx
  have hD : (fun x => φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)) =O[𝓝 0]
      fun x => ‖x‖ ^ 3 := by
    have hE := defect_expansion_at hρ₀ hTay' w v k₂ L (specProj v w) hμ hLk
    refine (((orbitEmb m θ L).isBigO_comp _ _).trans hE).congr' ?_ EventuallyEq.rfl
    filter_upwards [hev₂] with x hx
    have hΨφ : coordInv v hm (x, φ x) = x 0 • v + x 0 ^ 2 • k₂ := by
      rw [coordInv_apply]
      show x 0 • v + orbitEmb m θ L (x 0 ^ 2 • k₂) ⟨0, hm⟩ = _
      rw [orbitEmb_zero]
    have hNe := hNcN _ hx
    have hfφ : f (x, φ x) = centreCoord w (nonlin P p M (x 0 • v + x 0 ^ 2 • k₂)) := by
      simp only [hfdef, cutF, hΨφ, hNe]; rfl
    have hgφ : g (x, φ x) =
        orbitEmb m θ L (specProj v w (nonlin P p M (x 0 • v + x 0 ^ 2 • k₂))) := by
      simp only [hgdef, cutG, hΨφ, hNe]; rfl
    have hc : (A x + f (x, φ x)) 0 = μ * x 0 + w (nonlin P p M (x 0 • v + x 0 ^ 2 • k₂)) := by
      rw [hfφ]; simp [hAdef, centreCoord_apply_zero]
    show orbitEmb m θ L _ = φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)
    rw [hgφ]
    simp only [hφdef]
    rw [hc, hBdef, orbitShift_orbitEmb hm hθ0.ne', L.map_smul (x 0 ^ 2) k₂]
    simp only [map_sub, map_smul]
  have happrox := Map.CenterManifold.isBigO_sub_of_defect hAs hA hB hθ0.le hfl hgl hf0 hg0
    (by simpa using hεa) hh hh0 hinv hφ hφ0 (by norm_num : 1 ≤ 3) hD (by simpa using hκq)
    (by simpa using hκ1)
  -- the stable coordinate of the centre manifold is `(x 0)² k₂ + O(‖x‖³)`
  set π₀ : (Fin m → ℝⁿ) →L[ℝ] ℝⁿ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n)) ⟨0, hm⟩
    with hπ₀
  have hy : (fun x : ℝ¹ => h x ⟨0, hm⟩ - x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    refine ((π₀.isBigO_comp _ _).trans happrox).congr_left fun x => ?_
    show (h x - orbitEmb m θ L (x 0 ^ 2 • k₂)) ⟨0, hm⟩ = _
    rw [Pi.sub_apply, orbitEmb_zero]
  -- the reduced map
  have hred := reduced_expansion hρ₀ hTay' w v k₂ hy
  have hev : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + h x ⟨0, hm⟩‖ ≤ ρ₁ := by
    have hy1 : (fun x : ℝ¹ => h x ⟨0, hm⟩) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
      have := (hy.trans (isBigO_norm_pow_of_le (by norm_num : 1 ≤ 3))).add
        ((isBigO_smul_const (isBigO_coord_pow 2) k₂).trans
          (isBigO_norm_pow_of_le (by norm_num : 1 ≤ 2)))
      exact this.congr_left fun x => sub_add_cancel _ _
    have := (((isBigO_smul_const hu1' v).add hy1).trans_tendsto hnorm0).eventually
      (Metric.closedBall_mem_nhds 0 hρ₁)
    filter_upwards [this] with x hx
    simpa using hx
  set a := w (P₂ v v) with ha
  set b := w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) with hb
  have hr : (fun x : ℝ¹ => Map.CenterManifold.reducedMap A f h x 0 -
      (μ * x 0 + a * x 0 ^ 2 + b * x 0 ^ 3)) =O[𝓝 0] fun x => ‖x‖ ^ 4 := by
    refine hred.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with x hx
    have hΨh : coordInv v hm (x, h x) = x 0 • v + h x ⟨0, hm⟩ := by rw [coordInv_apply]
    have hfh : f (x, h x) = centreCoord w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
      simp only [hfdef, cutF, hΨh, hNcN _ hx]; rfl
    have hc : Map.CenterManifold.reducedMap A f h x 0 =
        μ * x 0 + w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
      rw [Map.CenterManifold.reducedMap, hfh]; simp [hAdef, centreCoord_apply_zero]
    rw [hc]
    ring
  obtain ⟨C, hC⟩ := hr.bound
  obtain ⟨r₀, hr₀, hCb⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨Map.CenterManifold.reducedMap A f h, ⟨r₀ / 2, C, half_pos hr₀, fun y hy => ?_⟩,
    fun hr => localAsymptoticStable_of_translate
      (Map.CenterManifold.localAsymptoticStable_of_reduced hB hθ0.le hfl hgl hθ2 hh hh0 hinv
        (coordInv_coordMap hm θ) hρ₁ hG hr),
    ⟨fun hr => lyapunovStable_of_translate
      (Map.CenterManifold.lyapunovStable_of_reduced hAs hA hB hθ0.le hfl hgl
        (by simpa using hgap) hθ2 hh hh0 hinv (coordInv_coordMap hm θ) hρ₁ hG hr),
    fun hLS => Map.CenterManifold.lyapunovStable_reduced hh hh0 hinv hgraph hρ₁ hG
      (lyapunovStable_translate hLS)⟩, ρ₁, hρ₁, fun e he hfix => ?_⟩
  · have := hCb (show dist y 0 < r₀ by rw [dist_zero_right]; linarith)
    rw [Real.norm_eq_abs, norm_pow, norm_norm, NormalForm.norm_state1] at this
    exact this
  · -- a fixed point near `p` lies on the centre manifold
    have hGe : Φ e = Map.CenterManifold.splitMap A B f g (Φ e) := by
      have := hG e he
      simp only [hfix, add_sub_cancel_left] at this
      exact this
    have hatt := Map.CenterManifold.norm_splitMap_sub_graph_le hB hfl hgl hh hinv (Φ e)
    rw [← hGe] at hatt
    have hon : (Φ e).2 = h (Φ e).1 := by
      obtain ⟨d, hd⟩ : ∃ d, d = ‖(Φ e).2 - h (Φ e).1‖ := ⟨_, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = θ + 2 * ε := ⟨_, rfl⟩
      rw [← hd, ← hc] at hatt
      have hc1 : 0 < 1 - c := by rw [hc]; linarith
      have hd0 : 0 ≤ d := by rw [hd]; exact norm_nonneg _
      have h1 : (1 - c) * d ≤ (1 - c) * 0 := by linarith
      have h0 : d ≤ 0 := le_of_mul_le_mul_left h1 hc1
      rw [hd] at h0
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
    have hΦ1 : (Φ e).1 = centreCoord w e := rfl
    have hpair : Φ e = ((Φ e).1, h (Φ e).1) := Prod.ext rfl hon
    refine ⟨?_, fun hwe => ?_⟩
    · rw [← hΦ1]
      show A (Φ e).1 + f ((Φ e).1, h (Φ e).1) = (Φ e).1
      rw [← hpair]
      exact (congrArg Prod.fst hGe).symm
    · have hx0 : (Φ e).1 = 0 := by
        rw [hΦ1]; simp [centreCoord, hwe]
      have hz : Φ e = 0 := by rw [hpair, hx0]; exact Prod.ext rfl hh0
      rw [← coordInv_coordMap (M := reflect M v w μ) (w := w) hm θ e]
      show Ψ (Φ e) = 0
      rw [hz, map_zero]

open Matrix in
/-- **What the spectral hypothesis says about the multipliers** (matrix form, a real multiplier
`μ` with `|μ| ≥ 1`). For a real matrix `M` with `M v = μ v`, `wᵀ M = μ wᵀ`, `w ⬝ v = 1` and
Schur stable deflated matrix `M − μ v wᵀ`: every complex multiplier of `M` other than `μ` lies
strictly inside the unit circle, every complex eigenvector of `μ` is a multiple of `v`, and there
is no Jordan chain at `μ` (`(M − μ I) z = v` has no solution): `μ` is a simple multiplier. For
`μ = −1` this is the content of `FlipReduction.multipliers_of_deflate`. -/
@[tmio T, powerlib_foundation] theorem multipliers_of_deflateAt {Mm : Matrix (Fin n) (Fin n) ℝ}
    {vm wm : Fin n → ℝ} (hμ : 1 ≤ |μ|) (hv : Mm *ᵥ vm = μ • vm) (hw : wm ᵥ* Mm = μ • wm)
    (hwv : wm ⬝ᵥ vm = 1) (hS : LTI.SchurStable (Mm - μ • Matrix.vecMulVec vm wm)) :
    (∀ (ν : ℂ) (z : Fin n → ℂ), z ≠ 0 → Mm.map (algebraMap ℝ ℂ) *ᵥ z = ν • z →
      ν = μ ∨ ‖ν‖ < 1) ∧
    (∀ z : Fin n → ℂ, Mm.map (algebraMap ℝ ℂ) *ᵥ z = (μ : ℂ) • z →
      z = ((algebraMap ℝ ℂ ∘ wm) ⬝ᵥ z) • (algebraMap ℝ ℂ ∘ vm)) ∧
    ¬ ∃ z : Fin n → ℂ, (Mm.map (algebraMap ℝ ℂ) - (μ : ℂ) • 1) *ᵥ z = algebraMap ℝ ℂ ∘ vm := by
  set f := algebraMap ℝ ℂ with hf
  set Mc := Mm.map f with hMc
  set vc := f ∘ vm with hvc
  set wc := f ∘ wm with hwc
  have hfμ : f μ = (μ : ℂ) := rfl
  have hvM : Mc *ᵥ vc = (μ : ℂ) • vc := by
    funext i
    have := RingHom.map_mulVec f Mm vm i
    rw [hv] at this
    rw [← this]; simp [hvc, hfμ]
  have hwM' : wc ᵥ* Mc = (μ : ℂ) • wc := by
    funext i
    have := RingHom.map_vecMul f Mm wm i
    rw [hw] at this
    rw [← this]; simp [hwc, hfμ]
  have hwv' : wc ⬝ᵥ vc = 1 := by
    have := RingHom.map_dotProduct f wm vm
    rw [hwv, map_one] at this
    exact this.symm
  have hLc : (Mm - μ • Matrix.vecMulVec vm wm).map f = Mc - (μ : ℂ) • Matrix.vecMulVec vc wc := by
    ext i j; simp [Matrix.vecMulVec_apply, hMc, hvc, hwc, hfμ]
  have hwM : ∀ z, wc ⬝ᵥ (Mc *ᵥ z) = (μ : ℂ) * (wc ⬝ᵥ z) := fun z => by
    rw [Matrix.dotProduct_mulVec, hwM', smul_dotProduct, smul_eq_mul]
  have hL : ∀ z, (Mc - (μ : ℂ) • Matrix.vecMulVec vc wc) *ᵥ z =
      Mc *ᵥ z - ((μ : ℂ) * (wc ⬝ᵥ z)) • vc := fun z => by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
      smul_smul]
  have hnorm : ‖(μ : ℂ)‖ = |μ| := Complex.norm_real μ
  refine ⟨fun ν z hz hMz => ?_, fun z hMz => ?_, ?_⟩
  · have h1 : (ν - μ) * (wc ⬝ᵥ z) = 0 := by
      have := hwM z
      rw [hMz, dotProduct_smul, smul_eq_mul] at this
      linear_combination this
    rcases mul_eq_zero.mp h1 with h | h
    · left; linear_combination h
    · right
      refine hS ν z hz ?_
      rw [hLc, hL, h, mul_zero, zero_smul, sub_zero, hMz]
  · set z' := z - (wc ⬝ᵥ z) • vc with hz'
    have hwz' : wc ⬝ᵥ z' = 0 := by
      rw [hz', dotProduct_sub, dotProduct_smul, hwv', smul_eq_mul, mul_one, sub_self]
    have hMz' : Mc *ᵥ z' = (μ : ℂ) • z' := by
      rw [hz', Matrix.mulVec_sub, Matrix.mulVec_smul, hMz, hvM, smul_sub, smul_comm]
    by_contra hne
    have hz'0 : z' ≠ 0 := fun h0 => hne (by rw [← sub_eq_zero, ← hz', h0])
    have := hS (μ : ℂ) z' hz'0 (by rw [hLc, hL, hwz', mul_zero, zero_smul, sub_zero, hMz'])
    rw [hnorm] at this
    linarith
  · rintro ⟨z, hz⟩
    have := congrArg (fun u => wc ⬝ᵥ u) hz
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, hwM, hwv', smul_eq_mul, sub_self] at this
    exact zero_ne_one this

/-! ## The multiplier `+1`: fold, transcritical and pitchfork types -/

/-- **The cubic coefficient and the choice of `k₂`.** Solutions of `(I − M) k₂ = Q P₂(v, v)`
differ by multiples of `v` (`eq_smul_of_apply_eq`), and
`b(k₂ + c v) = b(k₂) + 2 c a` with `a = w P₂(v, v)`: at a fold point with `a = 0` the cubic
coefficient `b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))` does not depend on the solution. -/
@[tmio T, powerlib_foundation] theorem cubicCoeff_add_smul (P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ)
    (w : ℝⁿ →L[ℝ] ℝ) (v k₂ : ℝⁿ) (c : ℝ) :
    w (P₂ v (k₂ + c • v) + P₂ (k₂ + c • v) v) = w (P₂ v k₂ + P₂ k₂ v) + 2 * c * w (P₂ v v) := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- A solution of `(I − M) k₂ = Q P₂(v, v)` at the multiplier `+1`, projected onto `ker w`, solves
the deflated equation `k − (M − v wᵀ) k = Q P₂(v, v)` of `exists_reduced_map_at`. -/
@[tmio T, powerlib_foundation] theorem specProj_sub_deflateAt (hv : M v = v) (hwv : w v = 1)
    {y k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = y) :
    specProj v w k₂ - deflateAt M v w 1 (specProj v w k₂) = y := by
  rw [deflateAt_apply, w_specProj hwv, mul_zero, zero_smul, sub_zero, specProj_apply, map_sub,
    map_smul, hv, ← hk₂]
  abel

/-- The reduced map at the multiplier `+1` for an arbitrary solution `k₂` of
`(I − M) k₂ = Q P₂(v, v)`: `r(x) = x + a x² + (b(k₂) − 2 (w k₂) a) x³ + O(x⁴)`. -/
@[tmio T, powerlib_foundation] private theorem exists_reduced_map_one {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v) (hw : ∀ e, w (M e) = w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflateAt M v w 1 ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v)) :
    ∃ r : ℝ¹ → ℝ¹, (∃ ρ K' : ℝ, 0 < ρ ∧ ∀ y : ℝ¹, ‖y‖ ≤ ρ →
        |r y 0 - (y 0 + w (P₂ v v) * y 0 ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) -
          2 * w k₂ * w (P₂ v v)) * y 0 ^ 3)| ≤ K' * |y 0| ^ 4) ∧
      (Map.LocalAsymptoticStable r 0 → Map.LocalAsymptoticStable P p) ∧
      (Map.LyapunovStable r 0 ↔ Map.LyapunovStable P p) ∧
      ∃ ρ' > 0, ∀ e, ‖e‖ < ρ' → P (p + e) = p + e →
        r (centreCoord w e) = centreCoord w e ∧ (w e = 0 → e = 0) := by
  obtain ⟨r, ⟨ρ, K', hρ, hb⟩, hS, hU, hfix⟩ := exists_reduced_map_at (μ := 1) (by simp) hP hPp
    (by rw [hv, one_smul]) (fun e => by rw [hw, one_mul]) hwv hm hLm hρ₀ hTay
    (specProj_sub_deflateAt hv hwv hk₂)
  refine ⟨r, ⟨ρ, K', hρ, fun y hy => ?_⟩, hS, hU, hfix⟩
  have hQ : specProj v w k₂ = k₂ + (-w k₂) • v := by rw [specProj_apply]; module
  have hb' := cubicCoeff_add_smul P₂ w v k₂ (-w k₂)
  rw [← hQ] at hb'
  have := hb y hy
  rw [hb'] at this
  convert this using 3
  ring

/-- **Fold / transcritical type: unstable.** Let `P` fix `p` with strict derivative `M`, `M v = v`,
`w ∘ M = w`, `w v = 1`, a power of the deflated map `M − v wᵀ` of norm below one (the multiplier
`+1` simple, every other multiplier strictly inside the unit circle), and the cubic Taylor
expansion `P(p + e) = p + M e + P₂ e e + P₃(e, e, e) + O(‖e‖⁴)`. If the fold coefficient
`a = w P₂(v, v)` is not zero, `p` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_foldCoeff_ne_zero {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v) (hw : ∀ e, w (M e) = w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflateAt M v w 1 ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (ha : w (P₂ v v) ≠ 0) : Map.Unstable P p := by
  obtain ⟨k₀, hk₀⟩ := exists_sub_apply_eq hLm (specProj v w (P₂ v v))
  obtain ⟨r, ⟨ρ, K', hρ, hb⟩, -, hU, -⟩ := exists_reduced_map_at (μ := 1) (by simp) hP hPp
    (by rw [hv, one_smul]) (fun e => by rw [hw, one_mul]) hwv hm hLm hρ₀ hTay hk₀
  set b := w (P₃ (fun _ => v)) + w (P₂ v k₀ + P₂ k₀ v) with hbdef
  refine fun hLS => Map.quadratic_unstable (K := |b| + |K'| * ρ) hρ ha (fun y hy => ?_)
    (hU.2 hLS)
  have h1 := hb y hy
  have hy0 : |y 0| ≤ ρ := by rw [← NormalForm.norm_state1]; exact hy
  set u := y 0 with hu
  have hX := abs_nonneg u
  have h4 : K' * |u| ^ 4 ≤ |K'| * ρ * |u| ^ 3 := by
    calc K' * |u| ^ 4 ≤ |K'| * (|u| * |u| ^ 3) := by
          rw [← pow_succ']; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |K'| * (ρ * |u| ^ 3) := by gcongr
      _ = |K'| * ρ * |u| ^ 3 := by ring
  have h3 : |b * u ^ 3| = |b| * |u| ^ 3 := by rw [abs_mul, abs_pow]
  calc |r y 0 - (u + w (P₂ v v) * u ^ 2)|
      = |(r y 0 - (1 * u + w (P₂ v v) * u ^ 2 + b * u ^ 3)) + b * u ^ 3| := by ring_nf
    _ ≤ |r y 0 - (1 * u + w (P₂ v v) * u ^ 2 + b * u ^ 3)| + |b * u ^ 3| := abs_add_le _ _
    _ ≤ K' * |u| ^ 4 + |b| * |u| ^ 3 := by rw [h3]; exact add_le_add_left h1 _
    _ ≤ (|b| + |K'| * ρ) * |u| ^ 3 := by nlinarith

/-- **Pitchfork type, stable side.** Under the hypotheses of `unstable_of_foldCoeff_ne_zero`, let
the fold coefficient vanish, `a = w P₂(v, v) = 0`, and let `k₂` be a solution of
`(I − M) k₂ = Q P₂(v, v)` (`Q e = e − (w e) v`). If the cubic coefficient
`b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))` is negative (it does not depend on the choice of
`k₂`, `cubicCoeff_add_smul`), `p` is locally asymptotically stable, and never locally
exponentially stable (the multiplier `+1`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_cubicCoeff_neg {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v)
    (hw : ∀ e, w (M e) = w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflateAt M v w 1 ^ m‖ < 1) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v)) (ha : w (P₂ v v) = 0)
    (hb : w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) < 0) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨r, ⟨ρ, K', hρ, hr⟩, hS, -, -⟩ :=
    exists_reduced_map_one hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂
  refine ⟨hS (Map.cubic_localAsymptoticStable (K := K') hρ hb fun y hy => ?_), ?_⟩
  · have := hr y hy
    rw [ha] at this
    convert this using 3
    ring
  · have hv0 : v ≠ 0 := by rintro rfl; simp at hwv
    exact Map.not_locallyExponentiallyStable_of_eigenvector hP.hasFDerivAt hPp hv0
      (μ := 1) (by rw [hv, one_smul]) (by norm_num)

/-- **Pitchfork type, unstable side.** Under the hypotheses of
`localAsymptoticStable_of_cubicCoeff_neg`, a positive cubic coefficient `b` makes `p` unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_cubicCoeff_pos {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v) (hw : ∀ e, w (M e) = w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflateAt M v w 1 ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v)) (ha : w (P₂ v v) = 0)
    (hb : 0 < w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) : Map.Unstable P p := by
  obtain ⟨r, ⟨ρ, K', hρ, hr⟩, -, hU, -⟩ :=
    exists_reduced_map_one hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂
  refine fun hLS => Map.cubic_unstable (K := K') hρ hb (fun y hy => ?_) (hU.2 hLS)
  have := hr y hy
  rw [ha] at this
  convert this using 3
  ring

/-- **Matrix form, fold type.** As `unstable_of_foldCoeff_ne_zero`, with the deflated monodromy
given by a Schur stable matrix `Lm` (`Linear.op Lm = M − v wᵀ`, `LTI.SchurStable Lm`; for a
monodromy matrix `Mm`, `Lm = Mm − v wᵀ`, see `multipliers_of_deflateAt`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_foldCoeff_ne_zero_matrix {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v)
    (hw : ∀ e, w (M e) = w e) (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ}
    (hL : Linear.op Lm = deflateAt M v w 1) (hS : LTI.SchurStable Lm)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (ha : w (P₂ v v) ≠ 0) : Map.Unstable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact unstable_of_foldCoeff_ne_zero hP hPp hv hw hwv hm hLm hρ₀ hTay ha

/-- **Matrix form, pitchfork type, stable side.** As `localAsymptoticStable_of_cubicCoeff_neg`,
with the deflated monodromy given by a Schur stable matrix `Lm`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_cubicCoeff_neg_matrix
    {P : ℝⁿ → ℝⁿ} {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v)
    (hw : ∀ e, w (M e) = w e) (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ}
    (hL : Linear.op Lm = deflateAt M v w 1) (hS : LTI.SchurStable Lm)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v)) (ha : w (P₂ v v) = 0)
    (hb : w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) < 0) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact localAsymptoticStable_of_cubicCoeff_neg hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ ha hb

/-- **Matrix form, pitchfork type, unstable side.** As `unstable_of_cubicCoeff_pos`, with the
deflated monodromy given by a Schur stable matrix `Lm`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_cubicCoeff_pos_matrix {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v)
    (hw : ∀ e, w (M e) = w e) (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ}
    (hL : Linear.op Lm = deflateAt M v w 1) (hS : LTI.SchurStable Lm)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v)) (ha : w (P₂ v v) = 0)
    (hb : 0 < w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) : Map.Unstable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact unstable_of_cubicCoeff_pos hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ ha hb

/-! ## A curve of fixed points: the reduction decides nothing -/

/-- A real number bounded by `C |u|` for arbitrarily small `u ≠ 0` is zero. -/
@[tmio T, powerlib_foundation] private theorem eq_zero_of_forall_abs_le {c C : ℝ}
    (h : ∀ δ > 0, ∃ u : ℝ, u ≠ 0 ∧ |u| < δ ∧ |c| ≤ C * |u|) : c = 0 := by
  by_contra hc
  have hc0 : 0 < |c| := abs_pos.mpr hc
  obtain ⟨u, -, hu, hcu⟩ := h (|c| / (|C| + 1)) (by positivity)
  have h1 : C * |u| ≤ |C| * |u| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg u)
  have h2 : |C| * |u| ≤ |C| * (|c| / (|C| + 1)) := mul_le_mul_of_nonneg_left hu.le (abs_nonneg C)
  have h3 : |C| * (|c| / (|C| + 1)) < |c| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg C]
  linarith

/-- A scalar map `x ↦ x + a x² + c x³ + O(x⁴)` with fixed points `u ≠ 0` arbitrarily close to `0`
has `a = c = 0`. -/
@[tmio T, powerlib_foundation] private theorem coeffs_eq_zero_of_fixed {a c K' : ℝ}
    (h : ∀ δ > 0, ∃ u : ℝ, u ≠ 0 ∧ |u| < δ ∧ |a * u ^ 2 + c * u ^ 3| ≤ K' * |u| ^ 4) :
    a = 0 ∧ c = 0 := by
  have hK4 : ∀ u : ℝ, |u| ≤ 1 → K' * |u| ^ 4 ≤ |K'| * |u| * |u| ^ 2 := fun u hu => by
    have h0 := abs_nonneg u
    calc K' * |u| ^ 4 ≤ |K'| * |u| ^ 4 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |K'| * |u| * |u| * |u| ^ 2 := by ring
      _ ≤ |K'| * |u| * 1 * |u| ^ 2 := by gcongr
      _ = |K'| * |u| * |u| ^ 2 := by ring
  have ha : a = 0 := eq_zero_of_forall_abs_le (C := |K'| + |c|) fun δ hδ => by
    obtain ⟨u, hu0, hu, hb⟩ := h (min δ 1) (lt_min hδ one_pos)
    refine ⟨u, hu0, hu.trans_le (min_le_left _ _), ?_⟩
    have hX : 0 < |u| := abs_pos.mpr hu0
    have hX1 : |u| ≤ 1 := hu.le.trans (min_le_right _ _)
    have t1 : |a * u ^ 2| ≤ |a * u ^ 2 + c * u ^ 3| + |c * u ^ 3| := by
      calc |a * u ^ 2| = |(a * u ^ 2 + c * u ^ 3) + -(c * u ^ 3)| := by ring_nf
        _ ≤ |a * u ^ 2 + c * u ^ 3| + |-(c * u ^ 3)| := abs_add_le _ _
        _ = |a * u ^ 2 + c * u ^ 3| + |c * u ^ 3| := by rw [abs_neg]
    have e1 : |a * u ^ 2| = |a| * |u| ^ 2 := by rw [abs_mul, abs_pow]
    have e2 : |c * u ^ 3| = |c| * |u| * |u| ^ 2 := by rw [abs_mul, abs_pow]; ring
    have t3 : |a| * |u| ^ 2 ≤ ((|K'| + |c|) * |u|) * |u| ^ 2 := by
      have := hK4 u hX1
      rw [← e1]
      nlinarith
    exact le_of_mul_le_mul_right t3 (by positivity)
  refine ⟨ha, eq_zero_of_forall_abs_le (C := |K'|) fun δ hδ => ?_⟩
  obtain ⟨u, hu0, hu, hb⟩ := h (min δ 1) (lt_min hδ one_pos)
  refine ⟨u, hu0, hu.trans_le (min_le_left _ _), ?_⟩
  have hX : 0 < |u| := abs_pos.mpr hu0
  have hX1 : |u| ≤ 1 := hu.le.trans (min_le_right _ _)
  rw [ha, zero_mul, zero_add, abs_mul, abs_pow] at hb
  have t : |c| * |u| ^ 3 ≤ (|K'| * |u|) * |u| ^ 3 := by
    calc |c| * |u| ^ 3 ≤ K' * |u| ^ 4 := hb
      _ ≤ |K'| * |u| ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = (|K'| * |u|) * |u| ^ 3 := by ring
  exact le_of_mul_le_mul_right t (by positivity)

/-- Fixed points other than `p` accumulating at `p` exclude local asymptotic stability: their
orbits are constant. -/
@[tmio T, powerlib_foundation] theorem not_localAsymptoticStable_of_fixedPoints {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hfix : ∀ δ > 0, ∃ q, P q = q ∧ q ≠ p ∧ ‖q - p‖ < δ) :
    ¬ Map.LocalAsymptoticStable P p := by
  rintro ⟨-, c, hc, hatt⟩
  obtain ⟨q, hq, hqp, hqd⟩ := hfix c hc
  have h1 := hatt q hqd
  have h2 : (fun k : ℕ => P^[k] q) = fun _ => q := funext fun k => Function.iterate_fixed hq k
  rw [h2] at h1
  exact hqp (tendsto_nhds_unique tendsto_const_nhds h1)

/-- **Accumulating fixed points: the coefficients vanish.** Under the hypotheses of
`unstable_of_foldCoeff_ne_zero` (a simple multiplier `+1` with stable complement), if fixed points
of `P` other than `p` accumulate at `p` — as along a curve of fixed points, such as a periodic
orbit of an autonomous system read through its period map — then the fold coefficient vanishes,
`a = w P₂(v, v) = 0`, the cubic coefficient vanishes, `b = 0` for every solution `k₂` of
`(I − M) k₂ = Q P₂(v, v)`, and `p` is not locally asymptotically stable. None of the three
verdicts of the reduction applies: the fixed points lie on the centre manifold, and the reduced
map fixes their centre coordinates. -/
@[tmio T, powerlib_foundation] theorem foldCoeffs_eq_zero_of_fixedPoints {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v)
    (hw : ∀ e, w (M e) = w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflateAt M v w 1 ^ m‖ < 1) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (hfix : ∀ δ > 0, ∃ q, P q = q ∧ q ≠ p ∧ ‖q - p‖ < δ) :
    w (P₂ v v) = 0 ∧ (∀ k₂, k₂ - M k₂ = specProj v w (P₂ v v) →
      w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) = 0) ∧ ¬ Map.LocalAsymptoticStable P p := by
  have key : ∀ k₂, k₂ - M k₂ = specProj v w (P₂ v v) → w (P₂ v v) = 0 ∧
      w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) - 2 * w k₂ * w (P₂ v v) = 0 := by
    intro k₂ hk₂
    obtain ⟨r, ⟨ρ, K', hρ, hr⟩, -, -, ρ', hρ', hfr⟩ :=
      exists_reduced_map_one hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂
    refine coeffs_eq_zero_of_fixed (K' := K') fun δ hδ => ?_
    set N := ‖w‖ + 1 with hN
    have hN0 : 0 < N := by positivity
    set δ' := min (min ρ' (ρ / N)) (δ / N) with hδ'
    have hδ'0 : 0 < δ' := lt_min (lt_min hρ' (by positivity)) (by positivity)
    obtain ⟨q, hq, hqp, hqd⟩ := hfix δ' hδ'0
    set e := q - p with he
    have hpe : p + e = q := by rw [he]; abel
    have hed : ‖e‖ < δ' := hqd
    obtain ⟨hre, hw0⟩ := hfr e (hed.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (by rw [hpe, hq])
    have he0 : e ≠ 0 := fun h0 => hqp (by rw [← hpe, h0, add_zero])
    have hu0 : w e ≠ 0 := fun h0 => he0 (hw0 h0)
    have hwe : |w e| ≤ N * ‖e‖ := by
      calc |w e| = ‖w e‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖w‖ * ‖e‖ := w.le_opNorm e
        _ ≤ N * ‖e‖ := by gcongr; linarith
    have hwe' : |w e| < N * δ' := hwe.trans_lt (by gcongr)
    have hcc : ‖centreCoord w e‖ = |w e| := by rw [NormalForm.norm_state1, centreCoord_apply_zero]
    refine ⟨w e, hu0, ?_, ?_⟩
    · calc |w e| < N * δ' := hwe'
        _ ≤ N * (δ / N) := by gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    · have hρe : ‖centreCoord w e‖ ≤ ρ := by
        rw [hcc]
        calc |w e| ≤ N * δ' := hwe'.le
          _ ≤ N * (ρ / N) := by gcongr; exact (min_le_left _ _).trans (min_le_right _ _)
          _ = ρ := by field_simp
      have := hr _ hρe
      rw [hre, centreCoord_apply_zero] at this
      have e : w e - (w e + w (P₂ v v) * w e ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) -
          2 * w k₂ * w (P₂ v v)) * w e ^ 3) = -(w (P₂ v v) * w e ^ 2 + (w (P₃ (fun _ => v)) +
          w (P₂ v k₂ + P₂ k₂ v) - 2 * w k₂ * w (P₂ v v)) * w e ^ 3) := by ring
      rwa [e, abs_neg] at this
  obtain ⟨k₀, hk₀⟩ := exists_sub_apply_eq hLm (specProj v w (P₂ v v))
  have hwk₀ : w k₀ = 0 := by
    have := congrArg w hk₀
    rwa [map_sub, w_deflateAt (μ := 1) (fun e => by rw [hw, one_mul]) hwv, w_specProj hwv,
      sub_zero] at this
  have hk₀' : k₀ - M k₀ = specProj v w (P₂ v v) := by
    rw [← hk₀, deflateAt_apply, hwk₀, mul_zero, zero_smul, sub_zero]
  have ha := (key k₀ hk₀').1
  refine ⟨ha, fun k₂ hk₂ => ?_, not_localAsymptoticStable_of_fixedPoints hfix⟩
  have := (key k₂ hk₂).2
  rw [ha, mul_zero, sub_zero] at this
  exact this

/-- **A curve of fixed points through `p`: Lyapunov stable, not asymptotically stable.** Under
the hypotheses of `unstable_of_foldCoeff_ne_zero` (a simple multiplier `+1` with stable
complement), let the fixed points of `P` near `p` realize every small value of the centre
coordinate: for every `δ > 0` there is `η > 0` such that each `u` with `|u| < η` is `w e` for a
fixed point `p + e`, `‖e‖ < δ` (a curve of fixed points transverse to `ker w`, such as a periodic
orbit of an autonomous system read through its period map). Then the reduced map is the identity
near `0`, so `p` is Lyapunov stable (`exists_reduced_map_at`, through the asymptotic phase), and
not locally asymptotically stable. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_fixedCurve {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = v) (hw : ∀ e, w (M e) = w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflateAt M v w 1 ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (hcurve : ∀ δ > 0, ∃ η > 0, ∀ u : ℝ, |u| < η →
      ∃ e, ‖e‖ < δ ∧ P (p + e) = p + e ∧ w e = u) :
    Map.LyapunovStable P p ∧ ¬ Map.LocalAsymptoticStable P p := by
  obtain ⟨k₀, hk₀⟩ := exists_sub_apply_eq hLm (specProj v w (P₂ v v))
  obtain ⟨r, -, -, hLy, ρ', hρ', hfr⟩ := exists_reduced_map_at (μ := 1) (by simp) hP hPp
    (by rw [hv, one_smul]) (fun e => by rw [hw, one_mul]) hwv hm hLm hρ₀ hTay hk₀
  obtain ⟨η, hη, hcη⟩ := hcurve ρ' hρ'
  have hid : ∀ y : ℝ¹, ‖y‖ < η → r y = y := fun y hy => by
    obtain ⟨e, he, hfix, hwe⟩ := hcη (y 0) (by rwa [← NormalForm.norm_state1])
    have hcc : centreCoord w e = y := by
      rw [eq_smul_single y]
      simp [centreCoord, hwe]
    rw [← hcc]
    exact (hfr e he hfix).1
  refine ⟨hLy.1 fun ε hε => ⟨min ε η, lt_min hε hη, fun y hy k => ?_⟩, ?_⟩
  · rw [sub_zero] at hy ⊢
    rw [Function.iterate_fixed (hid y (hy.trans_le (min_le_right _ _))) k]
    exact hy.trans_le (min_le_left _ _)
  · refine not_localAsymptoticStable_of_fixedPoints fun δ hδ => ?_
    obtain ⟨η₁, hη₁, hc₁⟩ := hcurve δ hδ
    obtain ⟨e, he, hfix, hwe⟩ := hc₁ (η₁ / 2) (by rw [abs_of_pos (by positivity)]; linarith)
    refine ⟨p + e, hfix, fun h0 => ?_, by rwa [add_sub_cancel_left]⟩
    have : e = 0 := by simpa using h0
    rw [this, map_zero] at hwe
    linarith

end powerlib.Periodic.FoldReduction
