import theorem.Periodic.PeriodMapJet
import theorem.Periodic.LocalField
import theorem.Map.DegenerateFlipCoefficients

/-! # The degenerate flip of a periodic solution, decided from the field

`theorem/Map/DegenerateFlipCoefficients.lean` decides a fixed point `p` of a map `P` with a
simple multiplier `−1`, a stable complement and a vanishing flip coefficient by the sign of
`c₅ + 3c₂c₄ − 2c₂⁴`, with `c₂, …, c₅` in closed form in the multilinear coefficients of a
fifth-order expansion of `P`, which it takes as a hypothesis. Here `P` is the period map
`P(ξ) = x(T; 0, ξ)` of a `T`-periodic system `ẋ = G(t, x)` at a `T`-periodic solution `x_*`, and
that hypothesis is derived from the field: `P(x_*(0)) = x_*(0)` (`FlowDerivative.periodMap_fixed`),
`DP(x_*(0)) = M = Φ(T, 0)`, the monodromy of the variational equation along `x_*`
(`FlowDerivative.hasStrictFDerivAt_periodMap`), and
`P(p + e) = p + M e + P₂(e, e) + P₃(e³) + P₄(e⁴) + P₅(e⁵) + O(‖e‖⁶)` with the coefficients
`Pⱼ = P_j(T)` of the variational hierarchy (`PeriodMapJet.flowJet`, `PeriodMapJet.periodMap_jet`
with `N = 5`); `P₂`, a multilinear map on `Fin 2`, is read as the bilinear map of the map
theorems (`bilin`). With `M vm = −vm`, `wmᵀ M = −wmᵀ`, `wm ⬝ vm = 1`, `Q x = x − (wm ⬝ x) vm`, the
homological equations

* `(I − M) k₂ = Q P₂(vm, vm)`,
* `(−I − M) k₃ = Q n₃ + 2c₂ k₂`, `wm ⬝ k₃ = 0`,
* `(I − M) k₄ = Q n₄ − (c₂² − 2c₃) k₂ − 3c₂ k₃`,

with `n₃ = curveCoeff₃ P₂ P₃ vm k₂`, `n₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃`,
`n₅ = curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄` (the coefficients of `tʲ` in
`P(p + t vm + t² k₂ + t³ k₃ + t⁴ k₄) − p − M(…)`, e.g. `n₃ = P₃(vm³) + P₂(vm, k₂) + P₂(k₂, vm)`),
`c₂ = wm ⬝ P₂(vm, vm)` and `cⱼ = wm ⬝ nⱼ`, give the coefficients
of the period map restricted to a centre manifold, `r(x) = −x + c₂x² + c₃x³ + c₄x⁴ + c₅x⁵ +
O(x⁶)`; `c₂` and `c₃` are the coefficients `a` and `b` of the flip coefficient `a² + b` of
`theorem/Periodic/FlipOrbit.lean`. If `a² + b = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ > 0`, the period map is
locally asymptotically, not exponentially, stable at `x_*(0)` and `x_*` is uniformly Lyapunov
stable and uniformly attracting from every initial time; if `c₅ + 3c₂c₄ − 2c₂⁴ < 0`, both are
unstable, with one escape radius for every initial time; the same holds for fields that are only
locally Lipschitz (the `_local` theorems, through `theorem/Periodic/LocalField.lean`). The map
statements are read on `ℝⁿ = EuclideanSpace ℝ (Fin n)` through `FlipOrbit.euclidMap`; the
coordinate change commutes with the closed forms (`localAsymptoticStable_of_degenerateFlip_coord`),
and the step from the period map to the solutions is `FlipOrbitUniform.uniformlyStable_of_map`
and `FlipOrbitUniform.uniformlyUnstable_of_map`.

Scope.
* As in `theorem/Periodic/FlipOrbit.lean`: solutions in `ℝ^{Fin n}` with the sup norm, the map
  semantics on `ℝⁿ` through `FlipOrbit.euclidMap`; `G` is `T`-periodic in `t` (`T > 0`),
  continuous, differentiable in `x` with `D_xG` jointly continuous, and globally `K`-Lipschitz in
  `x` (without the Lipschitz bound: the `_local` theorems below); `x_*` is a global solution with
  `x_*(T) = x_*(0)`.
* The regularity enters as the expansion of `PeriodMapJet.periodMap_jet` with `N = 5` along `x_*`
  on `[0, T]`: `G(r, x_* + u) = G(r, x_*) + D_xG u + ∑_{2 ≤ k ≤ 5} Q_k(r)(u, …, u) + O(‖u‖⁶)`
  with continuous coefficients `Q_k` (multilinear on `Fin k`, not assumed symmetric) and
  remainder `c ‖u‖⁶` for `‖u‖ ≤ ρ`; for a field of class `C⁶` in `x` with `D_x^kG` (`2 ≤ k ≤ 5`)
  continuous along `x_*` and `‖D_x⁶G‖` bounded on the tube it holds with `Q_k = D_x^kG/k!`
  (`PeriodMapJet.taylorSeries`, the `_of_contDiff` theorems). The coefficients of the period map
  are named in the statements by equations `P₂ = bilin (flowJet A Q 0 T 2)`,
  `Pⱼ = flowJet A Q 0 T j` (`A = jacobianAlong G x_*`), so that the closed forms read as in the
  map theorems.
* The spectral hypothesis is the projector form of `FlipReduction.multipliers_of_deflate` for
  `M = monodromy (jacobianAlong G x_*) T 0`: `−1` simple, every other multiplier strictly inside
  the unit circle (`M + vm wmᵀ` Schur stable). `k₂, k₃, k₄` are any solutions of the homological
  equations; they exist and are unique, `k₃` in `ker wm` (`exists_homological_coord`), so
  `c₄`, `c₅` are determined by the jet of the period map, `vm` and `wm`.
* The solution statements hold from every initial time `τ` with constants independent of `τ`
  (as in `theorem/Periodic/FlipOrbitUniform.lean`).
* Fields that are only locally Lipschitz (the `_local` theorems): `G` is localized by the smooth
  cut-off of `theorem/Periodic/LocalField.lean` (`LocalField.localField`) with a radius beyond the
  orbit and the tube of the expansion; the localized field has the same solution, Jacobian, jet
  and verdict, and its period map is the period map of `G` near `x_*(0)`
  (`periodMap_localField`). The transfer of the verdicts back to `G`
  (`uniformlyStable_local_of_map`, `uniformlyUnstable_local_of_map`) is the argument of the two
  theorems of `LocalField`, stated here once for any verdict of the localized period map; the
  escaping solutions of the unstable side are solutions on segments `[τ, t]`.
* `c₅ + 3c₂c₄ − 2c₂⁴ = 0` is not decided (the next odd order is needed, and no finite order
  suffices in general: `Map.flat_jet_undecided`).
* Generic mathematics; no model family.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.4 (the Poincaré map of a
periodic orbit, its derivative the monodromy matrix, its Taylor coefficients from the variational
equations; the projection method) and §9.5 (the degenerate flip); Kuznetsov and Meijer,
"Numerical normal forms for codim 2 bifurcations of fixed points with at most two critical
eigenvalues", SIAM J. Sci. Comput. 26 (2005) (the fifth-order coefficient of the degenerate flip
from the multilinear forms of the map); Hartman, *Ordinary Differential Equations*, Ch. V (the
higher variational equations); the open items of `theorem/Map/DegenerateFlipCoefficients.lean`
(Scope: for a period map the fifth-order expansion "is to be derived from the field; it is not
derived here") and `theorem/Periodic/FlipOrbit.lean` (Scope: "the degenerate flip `a² + b = 0`
is not decided here").

Results.
* `bilin`, `bilin_apply`, `bilin_diag` — a continuous multilinear map on `Fin 2` read as a
  continuous bilinear map.
* `localAsymptoticStable_of_degenerateFlip_coord`, `unstable_of_degenerateFlip_coord` — the
  degenerate flip of `DegenerateFlipCoefficients` (its matrix forms) for a map of `Fin n → ℝ` with
  coordinate data, read on `ℝⁿ`; `exists_homological_coord` — the homological equations in
  coordinates are uniquely solvable.
* `periodMap_data_five` — the strict derivative, the fixed point and the fifth-order expansion of
  the period map of a periodic solution, from the field.
* **The theorems**: `orbit_stable_of_degenerateFlip` (`a² + b = 0`, `c₅ + 3c₂c₄ − 2c₂⁴ > 0`: the
  period map is locally asymptotically, not exponentially, stable at `x_*(0)`, and `x_*` is
  uniformly Lyapunov stable and uniformly attracting) and `orbit_unstable_of_degenerateFlip`
  (`< 0`: the period map and `x_*` are unstable, one escape radius for every initial time);
  `orbit_stable_of_degenerateFlip_of_contDiff`, `orbit_unstable_of_degenerateFlip_of_contDiff` —
  the same for a field of class `C⁶` in `x`, with `Q_k = D_x^kG/k!` along `x_*`.
* Locally Lipschitz fields: `periodMap_localField` (the period map of the localized field is the
  local period map of `G`), `uniformlyStable_local_of_map`, `uniformlyUnstable_local_of_map`
  (the verdicts of the localized period map for the solutions of `G`);
  `orbit_stable_of_degenerateFlip_local`, `orbit_unstable_of_degenerateFlip_local`,
  `orbit_stable_of_degenerateFlip_of_contDiff_local`,
  `orbit_unstable_of_degenerateFlip_of_contDiff_local` — the degenerate flip for fields without
  a global Lipschitz bound.

Corrections.
None: an extension (the degenerate flip of `DegenerateFlipCoefficients` for the period map of a
periodic system, with its fifth-order expansion derived from the field).

Family and connection conclusions.
None: static evidence on periodic ODEs (stability of a periodic solution at a degenerate
period-doubling multiplier).
-/

noncomputable section
namespace powerlib.Periodic.DegenerateFlipOrbit

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor PeriodMapJet FlipOrbit FlipOrbitUniform FlipReduction

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The bilinear map of a coefficient on `Fin 2` -/

section Bilinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The continuous bilinear map `(a, b) ↦ f(a, b)` of a continuous multilinear map `f` on `Fin 2`
(Mathlib `ContinuousMultilinearMap.curryLeft`, then `continuousMultilinearCurryFin1`). -/
def bilin (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) : E →L[ℝ] E →L[ℝ] F :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
    ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F →L[ℝ] E →L[ℝ] F).comp f.curryLeft

@[tmio T, powerlib_foundation] theorem bilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) (a b : E) :
    bilin f a b = f ![a, b] := by
  show f (Fin.cons a (Fin.snoc 0 b)) = f ![a, b]
  congr 1
  funext i
  fin_cases i <;> rfl

@[tmio T, powerlib_foundation] theorem bilin_diag
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) (e : E) :
    bilin f e e = f (fun _ => e) := by
  rw [bilin_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

end Bilinear

/-! ## The degenerate flip of a map of `Fin n → ℝ` -/

section Coordinates

/-- **The degenerate flip in the coordinates `Fin n → ℝ`, both sides.** The hypotheses of the
matrix forms of `FlipReduction.localAsymptoticStable_of_degenerateFlip_taylor` for `euclidMap F`,
from the data of `F` in the coordinates `Fin n → ℝ` (sup norm): every coefficient is read on `ℝⁿ`
through `EuclideanSpace.equiv`, and `curveCoeff₃`, `curveCoeff₄`, `curveCoeff₅` commute with that
change of coordinates. -/
@[tmio T, powerlib_foundation] private theorem degenerateFlip_coords
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ C * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : Fin n → ℝ} (hk₂ : k₂ - Mm *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - Mm *ᵥ k₃ = curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
      (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - Mm *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0) :
    (0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
        3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
        2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 →
      Map.LocalAsymptoticStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) ∧
        ¬ Map.LocallyExponentiallyStable (euclidMap F)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm p)) ∧
    (wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
        3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
        2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0 →
      Map.Unstable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p)) := by
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (ε : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  -- the coefficients read on `ℝⁿ`
  set P₂E : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ :=
    ((ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝⁿ εS).comp P₂).bilinearComp εL εL
    with hP₂E
  have hP₂Ea : ∀ a b, P₂E a b = ε.symm (P₂ (ε a) (ε b)) := fun a b => by
    simp [hP₂E, hεS, hεL]
  have hconj : ∀ {j : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin n → ℝ)
      (Fin n → ℝ)) (a : ℝⁿ), εS.compContinuousMultilinearMap
        (f.compContinuousLinearMap fun _ => εL) (fun _ => a) = ε.symm (f (fun _ => ε a)) :=
    fun f a => by simp [hεS, hεL]
  have hlin : ∀ {j : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin n → ℝ)
      (Fin n → ℝ)) (a b : ℝⁿ), (εS.compContinuousMultilinearMap
        (f.compContinuousLinearMap fun _ => εL)).linearDeriv (fun _ => a) (fun _ => b) =
        ε.symm (f.linearDeriv (fun _ => ε a) (fun _ => ε b)) := by
    intro j f a b
    rw [ContinuousMultilinearMap.linearDeriv_apply, ContinuousMultilinearMap.linearDeriv_apply,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hu : (fun l => ε (Function.update (fun _ => a) i b l)) =
        Function.update (fun _ => ε a) i (ε b) := by
      funext l
      by_cases h : l = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hεS, hεL]
    rw [← hu]
    rfl
  set P₃E := εS.compContinuousMultilinearMap (P₃.compContinuousLinearMap fun _ => εL) with hP₃E
  set P₄E := εS.compContinuousMultilinearMap (P₄.compContinuousLinearMap fun _ => εL) with hP₄E
  set P₅E := εS.compContinuousMultilinearMap (P₅.compContinuousLinearMap fun _ => εL) with hP₅E
  set wE : ℝⁿ →L[ℝ] ℝ := (dotCLM wm).comp εL with hwE
  have hwEa : ∀ x, wE (ε.symm x) = wm ⬝ᵥ x := fun x => by
    show wm ⬝ᵥ ε (ε.symm x) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hop : ∀ x, Linear.op Mm (ε.symm x) = ε.symm (Mm *ᵥ x) := fun x => by
    show ε.symm (Mm *ᵥ ε (ε.symm x)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  set vE := ε.symm vm with hvE
  have hspec : ∀ x, specProj vE wE (ε.symm x) = ε.symm (x - (wm ⬝ᵥ x) • vm) := fun x => by
    rw [specProj_apply, hwEa, map_sub, map_smul]
  -- the coefficients of the candidate commute with the change of coordinates
  have hc₂ : P₂E vE vE = ε.symm (P₂ vm vm) := by
    rw [hP₂Ea, hvE, ContinuousLinearEquiv.apply_symm_apply]
  have hc₃ : curveCoeff₃ P₂E P₃E vE (ε.symm k₂) = ε.symm (curveCoeff₃ P₂ P₃ vm k₂) := by
    simp only [curveCoeff₃, hP₂Ea, hP₃E, hconj, hvE, ContinuousLinearEquiv.apply_symm_apply,
      map_add]
  have hc₄ : curveCoeff₄ P₂E P₃E P₄E vE (ε.symm k₂) (ε.symm k₃) =
      ε.symm (curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) := by
    simp only [curveCoeff₄, hP₂Ea, hP₃E, hP₄E, hconj, hlin, hvE,
      ContinuousLinearEquiv.apply_symm_apply, map_add]
  have hc₅ : curveCoeff₅ P₂E P₃E P₄E P₅E vE (ε.symm k₂) (ε.symm k₃) (ε.symm k₄) =
      ε.symm (curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄) := by
    simp only [curveCoeff₅, hP₂Ea, hP₃E, hP₄E, hP₅E, hconj, hlin, hvE,
      ContinuousLinearEquiv.apply_symm_apply, map_add]
  -- the data of `euclidMap F`
  have hP : HasStrictFDerivAt (euclidMap F) (Linear.op Mm) (ε.symm p) := by
    have h1 : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap (ε (ε.symm p)) := by
      rwa [ContinuousLinearEquiv.apply_symm_apply]
    have h := (ε.symm.hasStrictFDerivAt (x := F (ε (ε.symm p)))).comp (ε.symm p)
      (h1.comp (ε.symm p) ε.hasStrictFDerivAt)
    have hfun : euclidMap F = fun x => ε.symm (F (ε x)) := rfl
    have hM : Linear.op Mm = (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ).comp
        ((Matrix.toLin' Mm).toContinuousLinearMap.comp (ε : ℝⁿ →L[ℝ] (Fin n → ℝ))) := by
      ext1 y; rfl
    rw [hfun, hM]
    exact h
  have hPp : euclidMap F (ε.symm p) = ε.symm p := by
    show ε.symm (F (ε (ε.symm p))) = ε.symm p
    rw [ContinuousLinearEquiv.apply_symm_apply, hFp]
  have hv' : Linear.op Mm vE = -vE := by rw [hvE, hop, hv, map_neg]
  have hw' : ∀ e, wE (Linear.op Mm e) = -wE e := fun e => by
    show wm ⬝ᵥ ε (ε.symm (Mm *ᵥ ε e)) = -(wm ⬝ᵥ ε e)
    rw [ContinuousLinearEquiv.apply_symm_apply, Matrix.dotProduct_mulVec, hw, neg_dotProduct]
  have hwv' : wE vE = 1 := by rw [hvE, hwEa, hwv]
  have hL : Linear.op (Mm + vecMulVec vm wm) = deflate (Linear.op Mm) vE wE := by
    ext1 y
    rw [deflate_apply]
    show ε.symm ((Mm + vecMulVec vm wm) *ᵥ ε y) = ε.symm (Mm *ᵥ ε y) + (wm ⬝ᵥ ε y) • ε.symm vm
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, map_add, op_smul_eq_smul, map_smul]
  have hTay' : ∀ e, ‖e‖ ≤ ρ₀ / (‖εL‖ + 1) → ‖euclidMap F (ε.symm p + e) - ε.symm p -
      Linear.op Mm e - P₂E e e - P₃E (fun _ => e) - P₄E (fun _ => e) - P₅E (fun _ => e)‖ ≤
        ‖εS‖ * max C 0 * ‖εL‖ ^ 6 * ‖e‖ ^ 6 := by
    intro e he
    have hεe : ‖ε e‖ ≤ ρ₀ := by
      have h1 : ‖ε e‖ ≤ ‖εL‖ * ‖e‖ := εL.le_opNorm e
      have h2 : ‖εL‖ * ‖e‖ ≤ (‖εL‖ + 1) * ‖e‖ := by nlinarith [norm_nonneg e]
      have h3 : (‖εL‖ + 1) * ‖e‖ ≤ ρ₀ := by
        rw [le_div_iff₀ (by positivity)] at he; linarith
      linarith
    have hid : euclidMap F (ε.symm p + e) - ε.symm p - Linear.op Mm e - P₂E e e -
        P₃E (fun _ => e) - P₄E (fun _ => e) - P₅E (fun _ => e) =
        ε.symm (F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) - P₃ (fun _ => ε e) -
          P₄ (fun _ => ε e) - P₅ (fun _ => ε e)) := by
      have hE : euclidMap F (ε.symm p + e) = ε.symm (F (p + ε e)) := by
        show ε.symm (F (ε (ε.symm p + e))) = _
        rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
      have hope : Linear.op Mm e = ε.symm (Mm *ᵥ ε e) := rfl
      rw [hE, hP₂Ea, hP₃E, hP₄E, hP₅E, hconj, hconj, hconj, hope]
      simp only [map_sub]
    rw [hid]
    have hC : 0 ≤ max C 0 := le_max_right _ _
    have hT0 : ‖F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) - P₃ (fun _ => ε e) -
        P₄ (fun _ => ε e) - P₅ (fun _ => ε e)‖ ≤ max C 0 * ‖ε e‖ ^ 6 :=
      (hTay _ hεe).trans (by gcongr; exact le_max_left _ _)
    calc ‖ε.symm (F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) - P₃ (fun _ => ε e) -
          P₄ (fun _ => ε e) - P₅ (fun _ => ε e))‖
        ≤ ‖εS‖ * ‖F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) - P₃ (fun _ => ε e) -
          P₄ (fun _ => ε e) - P₅ (fun _ => ε e)‖ := εS.le_opNorm _
      _ ≤ ‖εS‖ * (max C 0 * ‖ε e‖ ^ 6) := by gcongr
      _ ≤ ‖εS‖ * (max C 0 * (‖εL‖ * ‖e‖) ^ 6) := by gcongr; exact εL.le_opNorm e
      _ = ‖εS‖ * max C 0 * ‖εL‖ ^ 6 * ‖e‖ ^ 6 := by ring
  have hρ : 0 < ρ₀ / (‖εL‖ + 1) := by positivity
  -- the homological equations on `ℝⁿ`
  have hk₂' : ε.symm k₂ - Linear.op Mm (ε.symm k₂) = specProj vE wE (P₂E vE vE) := by
    rw [hc₂, hspec, hop, ← map_sub, hk₂]
  have hk₃' : -ε.symm k₃ - Linear.op Mm (ε.symm k₃) =
      specProj vE wE (curveCoeff₃ P₂E P₃E vE (ε.symm k₂)) +
        (2 * wE (P₂E vE vE)) • ε.symm k₂ := by
    rw [hc₃, hspec, hc₂, hwEa, hop, ← map_neg, ← map_sub, hk₃, map_add, map_smul]
  have hwk₃' : wE (ε.symm k₃) = 0 := by rw [hwEa, hwk₃]
  have hk₄' : ε.symm k₄ - Linear.op Mm (ε.symm k₄) =
      specProj vE wE (curveCoeff₄ P₂E P₃E P₄E vE (ε.symm k₂) (ε.symm k₃)) -
        (wE (P₂E vE vE) ^ 2 - 2 * wE (curveCoeff₃ P₂E P₃E vE (ε.symm k₂))) • ε.symm k₂ -
          (3 * wE (P₂E vE vE)) • ε.symm k₃ := by
    rw [hc₄, hspec, hc₃, hc₂, hwEa, hwEa, hop, ← map_sub, hk₄, map_sub, map_sub, map_smul,
      map_smul]
  have hdeg' : wE (P₂E vE vE) ^ 2 + wE (curveCoeff₃ P₂E P₃E vE (ε.symm k₂)) = 0 := by
    rw [hc₂, hc₃, hwEa, hwEa, hdeg]
  have hκ : wE (curveCoeff₅ P₂E P₃E P₄E P₅E vE (ε.symm k₂) (ε.symm k₃) (ε.symm k₄)) +
      3 * wE (P₂E vE vE) * wE (curveCoeff₄ P₂E P₃E P₄E vE (ε.symm k₂) (ε.symm k₃)) -
        2 * wE (P₂E vE vE) ^ 4 =
      wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
        3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
        2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 := by
    rw [hc₅, hc₄, hc₂, hwEa, hwEa, hwEa]
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · exact localAsymptoticStable_of_degenerateFlip_taylor_matrix hP hPp hv' hw' hwv' hL hS hρ
      hTay' hk₂' hk₃' hwk₃' hk₄' hdeg' (hκ ▸ hpos)
  · exact unstable_of_degenerateFlip_taylor_matrix hP hPp hv' hw' hwv' hL hS hρ
      hTay' hk₂' hk₃' hwk₃' hk₄' hdeg' (hκ ▸ hneg)

/-- **The degenerate flip in the coordinates `Fin n → ℝ`, stable side.** Let a map `F` of
`Fin n → ℝ` (sup norm) fix `p` with strict derivative `Mm` there, let `Mm vm = −vm`,
`wmᵀ Mm = −wmᵀ`, `wm ⬝ vm = 1` and `Mm + vm wmᵀ` be Schur stable (a simple multiplier `−1` with
stable complement), let `F` have the fifth-order expansion
`‖F(p + e) − p − Mm e − P₂(e, e) − P₃(e³) − P₄(e⁴) − P₅(e⁵)‖ ≤ C ‖e‖⁶` on `‖e‖ ≤ ρ₀`, and let
`k₂, k₃, k₄` solve the homological equations of `FlipReduction.defect_expansion_five` in these
coordinates (`Q x = x − (wm ⬝ x) vm`): `(I − Mm) k₂ = Q P₂(vm, vm)`,
`(−I − Mm) k₃ = Q n₃ + 2c₂ k₂`, `wm ⬝ k₃ = 0`, `(I − Mm) k₄ = Q n₄ − (c₂² − 2c₃) k₂ − 3c₂ k₃`,
with `n₃ = curveCoeff₃ P₂ P₃ vm k₂`, `n₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃`,
`n₅ = curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄`, `c₂ = wm ⬝ P₂(vm, vm)`, `cⱼ = wm ⬝ nⱼ`. If the flip
coefficient vanishes, `c₂² + c₃ = 0`, and `c₅ + 3c₂c₄ − 2c₂⁴ > 0`, then `F` read on `ℝⁿ` is locally
asymptotically, not exponentially, stable at `p`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_degenerateFlip_coord
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ C * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : Fin n → ℝ} (hk₂ : k₂ - Mm *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - Mm *ᵥ k₃ = curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
      (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - Mm *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : 0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4) :
    Map.LocalAsymptoticStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) :=
  (degenerateFlip_coords hF hFp hv hw hwv hS hρ₀ hTay hk₂ hk₃ hwk₃ hk₄ hdeg).1 hκ

/-- **The degenerate flip in the coordinates `Fin n → ℝ`, unstable side.** Under the hypotheses
of `localAsymptoticStable_of_degenerateFlip_coord`, if `c₂² + c₃ = 0` and
`c₅ + 3c₂c₄ − 2c₂⁴ < 0`, then `F` read on `ℝⁿ` is unstable at `p`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_degenerateFlip_coord
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e) -
      P₄ (fun _ => e) - P₅ (fun _ => e)‖ ≤ C * ‖e‖ ^ 6)
    {k₂ k₃ k₄ : Fin n → ℝ} (hk₂ : k₂ - Mm *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - Mm *ᵥ k₃ = curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
      (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - Mm *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0) :
    Map.Unstable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) :=
  (degenerateFlip_coords hF hFp hv hw hwv hS hρ₀ hTay hk₂ hk₃ hwk₃ hk₄ hdeg).2 hκ

/-- **The homological equations in coordinates are uniquely solvable.** If `wmᵀ Mm = −wmᵀ`,
`wm ⬝ vm = 1` and `Mm + vm wmᵀ` is Schur stable, then for every `r` with `wm ⬝ r = 0` the
equation `(I − Mm) k = r` has exactly one solution, and `(−I − Mm) k = r` exactly one with
`wm ⬝ k = 0` (`FlipReduction.exists_homological`, read through `EuclideanSpace.equiv`). The right
sides of the equations for `k₂`, `k₃`, `k₄` of `localAsymptoticStable_of_degenerateFlip_coord`
lie in `ker wm`, so these exist and are unique one after the other, and `c₄`, `c₅` are functions
of `P₂, …, P₅`, `vm` and `wm`. -/
@[tmio T, powerlib_foundation] theorem exists_homological_coord
    {Mm : Matrix (Fin n) (Fin n) ℝ} {vm wm : Fin n → ℝ} (hw : wm ᵥ* Mm = -wm)
    (hwv : wm ⬝ᵥ vm = 1) (hS : LTI.SchurStable (Mm + vecMulVec vm wm)) {r : Fin n → ℝ}
    (hr : wm ⬝ᵥ r = 0) :
    (∃! k : Fin n → ℝ, k - Mm *ᵥ k = r) ∧
      ∃! k : Fin n → ℝ, wm ⬝ᵥ k = 0 ∧ -k - Mm *ᵥ k = r := by
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (ε : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set wE : ℝⁿ →L[ℝ] ℝ := (dotCLM wm).comp εL with hwE
  have hwEa : ∀ x, wE (ε.symm x) = wm ⬝ᵥ x := fun x => by
    show wm ⬝ᵥ ε (ε.symm x) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hop : ∀ x, Linear.op Mm (ε.symm x) = ε.symm (Mm *ᵥ x) := fun x => by
    show ε.symm (Mm *ᵥ ε (ε.symm x)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hw' : ∀ e, wE (Linear.op Mm e) = -wE e := fun e => by
    show wm ⬝ᵥ ε (ε.symm (Mm *ᵥ ε e)) = -(wm ⬝ᵥ ε e)
    rw [ContinuousLinearEquiv.apply_symm_apply, Matrix.dotProduct_mulVec, hw, neg_dotProduct]
  have hwv' : wE (ε.symm vm) = 1 := by rw [hwEa, hwv]
  have hL : Linear.op (Mm + vecMulVec vm wm) = deflate (Linear.op Mm) (ε.symm vm) wE := by
    ext1 y
    rw [deflate_apply]
    show ε.symm ((Mm + vecMulVec vm wm) *ᵥ ε y) = ε.symm (Mm *ᵥ ε y) + (wm ⬝ᵥ ε y) • ε.symm vm
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, map_add, op_smul_eq_smul, map_smul]
  obtain ⟨m, -, hm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hm
  obtain ⟨⟨k₁, hk₁, hu₁⟩, ⟨k₂, hk₂, hu₂⟩⟩ :=
    exists_homological hw' hwv' hm (by rw [hwEa, hr] : wE (ε.symm r) = 0)
  have e₁ : ∀ k, k - Mm *ᵥ k = r ↔ ε.symm k - Linear.op Mm (ε.symm k) = ε.symm r := fun k => by
    rw [hop, ← map_sub]; exact ε.symm.injective.eq_iff.symm
  have e₂ : ∀ k, (wm ⬝ᵥ k = 0 ∧ -k - Mm *ᵥ k = r) ↔
      (wE (ε.symm k) = 0 ∧ -ε.symm k - Linear.op Mm (ε.symm k) = ε.symm r) := fun k => by
    rw [hwEa, hop, ← map_neg, ← map_sub, ε.symm.injective.eq_iff]
  refine ⟨⟨ε k₁, (e₁ _).2 (by rwa [ContinuousLinearEquiv.symm_apply_apply]), fun k hk => ?_⟩,
    ⟨ε k₂, (e₂ _).2 (by rwa [ContinuousLinearEquiv.symm_apply_apply]), fun k hk => ?_⟩⟩
  · rw [← hu₁ _ ((e₁ k).1 hk), ContinuousLinearEquiv.apply_symm_apply]
  · rw [← hu₂ _ ((e₂ k).1 hk), ContinuousLinearEquiv.apply_symm_apply]

end Coordinates

/-! ## The degenerate flip of a periodic solution -/

section Orbit

variable {G : ℝ → (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

/-- **The period map to fifth order.** For a field `G` continuous, differentiable in `x` with
`D_xG` jointly continuous and `K`-Lipschitz in `x`, a solution `x_*` with `x_*(T) = x_*(0)` and
the expansion `G(r, x_* + u) = G(r, x_*) + D_xG u + ∑_{2 ≤ k ≤ 5} Q_k(r)(u, …, u) + O(‖u‖⁶)`
along `x_*` on `[0, T]` with continuous coefficients `Q_k`, the period map `P` has at
`p = x_*(0)` the strict derivative `M = Φ(T, 0)` (`FlowDerivative.hasStrictFDerivAt_periodMap`),
the fixed point `p`, and the fifth-order expansion
`‖P(p + e) − p − M e − P₂(e, e) − P₃(e³) − P₄(e⁴) − P₅(e⁵)‖ ≤ C ‖e‖⁶` near `0`
(`PeriodMapJet.periodMap_jet` with `N = 5`), with the coefficients `Pⱼ = flowJet A Q 0 T j` of the
variational hierarchy of `A = jacobianAlong G x_*` and `P₂` read as a bilinear map (`bilin`). -/
@[tmio T, powerlib_foundation] theorem periodMap_data_five
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q : ℝ → FormalMultilinearSeries ℝ (Fin n → ℝ) (Fin n → ℝ)}
    (hQ : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => Q r k) {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6) :
    HasStrictFDerivAt (periodMap hGc hK T)
      (Matrix.toLin' (monodromy (jacobianAlong G xs) T 0)).toContinuousLinearMap (xs 0) ∧
    periodMap hGc hK T (xs 0) = xs 0 ∧
    ∃ C ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ e, ‖e‖ ≤ ρ₀ →
      ‖periodMap hGc hK T (xs 0 + e) - xs 0 - monodromy (jacobianAlong G xs) T 0 *ᵥ e -
        bilin (flowJet (jacobianAlong G xs) Q 0 T 2) e e -
        flowJet (jacobianAlong G xs) Q 0 T 3 (fun _ => e) -
        flowJet (jacobianAlong G xs) Q 0 T 4 (fun _ => e) -
        flowJet (jacobianAlong G xs) Q 0 T 5 (fun _ => e)‖ ≤ C * ‖e‖ ^ 6 := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hA := continuous_jacobianAlong hD hxc
  refine ⟨hasStrictFDerivAt_periodMap hGc hGd hD hK hxs hT.le,
    periodMap_fixed hGc hK hxs hT.le hfix, ?_⟩
  obtain ⟨B, hB0, hB⟩ := exists_bound_coeff (Q := Q) (s := 0) (t := T) 5 hQ
  have hAK : ∀ r ∈ Icc 0 T, ∀ v, ‖jacobianAlong G xs r *ᵥ v‖ ≤ K * ‖v‖ := fun r _ v => by
    rw [jacobianAlong_mulVec]
    exact ((fderiv ℝ (G r) (xs r)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hK r)) (norm_nonneg v))
  have hTay' : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      jacobianAlong G xs r *ᵥ u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤
        c * ‖u‖ ^ (5 + 1) := fun r hr u hu => by
    rw [jacobianAlong_mulVec]; exact hTay r hr u hu
  refine ⟨flowConst K T B c 5, min 1 (ρ / Real.exp (K * T)), by positivity, fun e he => ?_⟩
  have h := periodMap_jet hGc hK hA (by norm_num) hQ hT.le hAK hB0 hB hxs hfix hTay' e he
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton,
    ← bilin_diag] at h
  convert h using 2
  abel

/-- **The degenerate flip of a periodic solution, stable side.** Let `G` be `T`-periodic in `t`,
continuous, differentiable in `x` with `D_xG` jointly continuous and `K`-Lipschitz in `x`, `x_*` a
solution with `x_*(T) = x_*(0)` along which `G` has on `[0, T]` the expansion of fifth order with
continuous coefficients `Q_k` (`2 ≤ k ≤ 5`) and remainder `c ‖u‖⁶` for `‖u‖ ≤ ρ`. Let the
monodromy `M = Φ(T, 0) = monodromy (jacobianAlong G x_*) T 0` have a simple multiplier `−1` with
stable complement (`M vm = −vm`, `wmᵀ M = −wmᵀ`, `wm ⬝ vm = 1`, `M + vm wmᵀ` Schur stable), let
`Pⱼ = flowJet (jacobianAlong G x_*) Q 0 T j` be the coefficients of the period map
(`periodMap_data_five`, `P₂` read bilinearly) and `k₂, k₃, k₄` solve the homological equations of
`localAsymptoticStable_of_degenerateFlip_coord` for them. If the flip coefficient vanishes,
`c₂² + c₃ = 0`, and `c₅ + 3c₂c₄ − 2c₂⁴ > 0` (`c₂ = wm ⬝ P₂(vm, vm)`, `c₃ = wm ⬝ n₃`,
`c₄ = wm ⬝ n₄`, `c₅ = wm ⬝ n₅`, `nⱼ = curveCoeffⱼ`), then the period map (read on `ℝⁿ`) is
locally asymptotically, not exponentially, stable at `x_*(0)`, and `x_*` is uniformly Lyapunov
stable and uniformly attracting from every initial time
(`FlipOrbitUniform.uniformlyStable_of_map`). -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_degenerateFlip
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q : ℝ → FormalMultilinearSeries ℝ (Fin n → ℝ) (Fin n → ℝ)}
    (hQ : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => Q r k) {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) Q 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) Q 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) Q 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) Q 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : 0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x G (Ici τ) →
      ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t → ‖x t - xs t‖ < ε := by
  subst hP₂ hP₃ hP₄ hP₅
  obtain ⟨hP, hPp, C, ρ₀, hρ₀, hTay'⟩ := periodMap_data_five hGc hGd hD hK hT hxs hfix hQ hρ hTay
  have hmap := localAsymptoticStable_of_degenerateFlip_coord hP hPp hv hw hwv hS hρ₀ hTay' hk₂
    hk₃ hwk₃ hk₄ hdeg hκ
  exact ⟨hmap, uniformlyStable_of_map hGc hK hT hGper hxs hfix hmap.1⟩

/-- **The degenerate flip of a periodic solution, unstable side.** Under the hypotheses of
`orbit_stable_of_degenerateFlip`, if `c₂² + c₃ = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ < 0`, the period map
(read on `ℝⁿ`) is unstable at `x_*(0)` and `x_*` is unstable with one escape radius for every
initial time (`FlipOrbitUniform.uniformlyUnstable_of_map`). -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_degenerateFlip
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q : ℝ → FormalMultilinearSeries ℝ (Fin n → ℝ) (Fin n → ℝ)}
    (hQ : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => Q r k) {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) Q 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) Q 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) Q 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) Q 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici τ) ∧
      ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  subst hP₂ hP₃ hP₄ hP₅
  obtain ⟨hP, hPp, C, ρ₀, hρ₀, hTay'⟩ := periodMap_data_five hGc hGd hD hK hT hxs hfix hQ hρ hTay
  have hmap := unstable_of_degenerateFlip_coord hP hPp hv hw hwv hS hρ₀ hTay' hk₂ hk₃ hwk₃ hk₄
    hdeg hκ
  exact ⟨hmap, uniformlyUnstable_of_map hGc hK hT hGper hxs hfix hmap⟩

/-- **Fields of class `C⁶`, stable side.** `orbit_stable_of_degenerateFlip` for a field with
`G(t, ·)` of class `C⁶`, `D_x^kG` continuous along `x_*` for `2 ≤ k ≤ 5` and
`‖D_x⁶G‖ ≤ B` on the tube of radius `ρ` about `x_*` over `[0, T]`: the coefficients of the field
are `Q_k = D_x^kG/k!` along `x_*` (`PeriodMapJet.taylorSeries G x_*`, remainder from
`PeriodMapJet.taylor_along_of_contDiff_order`), and those of the period map are
`Pⱼ = flowJet (jacobianAlong G x_*) (taylorSeries G x_*) 0 T j`. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_degenerateFlip_of_contDiff
    (hGc : Continuous (uncurry G)) (hG6 : ∀ t, ContDiff ℝ 6 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hDk : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => iteratedFDeriv ℝ k (G r) (xs r))
    {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 6 (G r) y‖ ≤ B)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : 0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x G (Ici τ) →
      ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t → ‖x t - xs t‖ < ε :=
  orbit_stable_of_degenerateFlip hGc (fun t => (hG6 t).differentiable (by norm_num)) hD hK hT
    hGper hxs hfix (fun k hk1 hk2 => (hDk k hk1 hk2).const_smul ((k.factorial : ℝ)⁻¹)) hρ
    (taylor_along_of_contDiff_order (by norm_num) (fun r _ y _ => (hG6 r).contDiffAt) hB)
    hv hw hwv hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hwk₃ hk₄ hdeg hκ

/-- **Fields of class `C⁶`, unstable side.** `orbit_unstable_of_degenerateFlip` with
`Q_k = D_x^kG/k!` along `x_*`, under the hypotheses of
`orbit_stable_of_degenerateFlip_of_contDiff`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_degenerateFlip_of_contDiff
    (hGc : Continuous (uncurry G)) (hG6 : ∀ t, ContDiff ℝ 6 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hDk : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => iteratedFDeriv ℝ k (G r) (xs r))
    {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 6 (G r) y‖ ≤ B)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici τ) ∧
      ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖ :=
  orbit_unstable_of_degenerateFlip hGc (fun t => (hG6 t).differentiable (by norm_num)) hD hK hT
    hGper hxs hfix (fun k hk1 hk2 => (hDk k hk1 hk2).const_smul ((k.factorial : ℝ)⁻¹)) hρ
    (taylor_along_of_contDiff_order (by norm_num) (fun r _ y _ => (hG6 r).contDiffAt) hB)
    hv hw hwv hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hwk₃ hk₄ hdeg hκ

end Orbit

/-! ## Fields without a global Lipschitz bound -/

section Local

open LocalField

variable {G : ℝ → (Fin n → ℝ) → Fin n → ℝ}

/-- **The period map of the localized field is the local period map of `G`.** For a field `G`
differentiable in `x` with `D_xG` jointly continuous, a solution `x_*` of `G` and a radius `R`
with `‖y‖ ≤ R` whenever `‖y − x_*(t)‖ ≤ 1`, let `G̃ = localField G R` (`LocalField.localField`)
be `K`-Lipschitz. From within `r = e^{−KT}` of `x_*(0)` a solution of `G` on `[0, T]` exists,
and every such solution ends at `P̃(x(0))`, `P̃` the period map of `G̃`: the flow of `G̃` from
there stays within `1` of `x_*` (Grönwall), so it solves `G`, and solutions of `G` are unique
(`LocalField.eqOn_of_isIntegralCurveOn_Icc_of_fderiv`). -/
@[tmio T, powerlib_foundation] theorem periodMap_localField
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {R : ℝ} {K : NNReal}
    (hGlc : Continuous (uncurry (localField G R))) (hK : ∀ t, LipschitzWith K (localField G R t))
    {T : ℝ} (hT : 0 ≤ T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ R) :
    ∃ r, 0 < r ∧ (∀ ξ, ‖ξ - xs 0‖ < r →
        ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = periodMap hGlc hK T (x 0) := by
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRnear t (xs t) (by simp))]; exact hxs t
  have hC0 : 0 < Real.exp (K * T) := Real.exp_pos _
  have hsol : ∀ ξ, ‖ξ - xs 0‖ < 1 / Real.exp (K * T) →
      IsIntegralCurveOn (flow hGlc hK 0 ξ) G (Icc 0 T) := by
    intro ξ hξ
    refine isIntegralCurveOn_of_localField
      ((flow_solution hGlc hK 0 ξ).mono Icc_subset_Ici_self) fun u hu => hRnear u _ ?_
    have h := dist_le_of_isIntegralCurveOn_Icc hK
      ((flow_solution hGlc hK 0 ξ).mono Icc_subset_Ici_self)
      (fun r _ => (hxsl r).hasDerivWithinAt) u hu
    rw [dist_eq_norm, dist_eq_norm, flow_start, sub_zero] at h
    have he : Real.exp (K * u) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hu.2 K.2)
    rw [lt_div_iff₀ hC0] at hξ
    calc ‖flow hGlc hK 0 ξ u - xs u‖ ≤ ‖ξ - xs 0‖ * Real.exp (K * u) := h
      _ ≤ ‖ξ - xs 0‖ * Real.exp (K * T) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ 1 := hξ.le
  refine ⟨1 / Real.exp (K * T), by positivity,
    fun ξ hξ => ⟨flow hGlc hK 0 ξ, flow_start hGlc hK 0 ξ, hsol ξ hξ⟩, fun x hx hx0 => ?_⟩
  exact eqOn_of_isIntegralCurveOn_Icc_of_fderiv hGd hD hx (hsol (x 0) hx0)
    (flow_start hGlc hK 0 (x 0)).symm ⟨hT, le_rfl⟩

/-- **From the localized period map to the solutions of `G`: stability.** In the setting of
`periodMap_localField`, with `G` `T`-periodic and `x_*(T) = x_*(0)`: if the period map of the
localized field `G̃ = localField G R` (read on `ℝⁿ`) is locally asymptotically stable at
`x_*(0)`, then `x_*` is uniformly Lyapunov stable as a solution of `G` (for every `ε` one `δ`
serves every initial time `τ` and every solution on a segment `[τ, t]`), the solutions of `G`
starting within some `δ` of `x_*(τ)` exist on `[τ, ∞)`, and they are uniformly attracted. The
verdict for `G̃` is `FlipOrbitUniform.uniformlyStable_of_map`; a solution of `G̃` within `1` of
`x_*` solves `G`, and conversely by uniqueness. -/
@[tmio T, powerlib_foundation] theorem uniformlyStable_local_of_map
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {R : ℝ} {K : NNReal}
    (hGlc : Continuous (uncurry (localField G R))) (hK : ∀ t, LipschitzWith K (localField G R t))
    {T : ℝ} (hT : 0 < T) (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ R)
    (h : Map.LocalAsymptoticStable (euclidMap (periodMap hGlc hK T))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ ≤ t →
      IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ (∀ (τ : ℝ) (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ →
        ∃ x : ℝ → Fin n → ℝ, x τ = ξ ∧ IsIntegralCurveOn x G (Ici τ)) ∧
      ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ + S ≤ t →
        IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε := by
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRnear t (xs t) (by simp))]; exact hxs t
  obtain ⟨hstab, δa, hδa, hatt⟩ :=
    uniformlyStable_of_map hGlc hK hT (periodic_localField hGper R) hxsl hfix h
  -- a solution of `G` along which the localized flow stays within `1` of `x_*` is that flow
  have heqOn : ∀ {τ t : ℝ} {x : ℝ → Fin n → ℝ}, IsIntegralCurveOn x G (Icc τ t) →
      (∀ u ∈ Icc τ t, ‖flow hGlc hK τ (x τ) u - xs u‖ ≤ 1) →
      EqOn x (flow hGlc hK τ (x τ)) (Icc τ t) := fun hx hnear =>
    eqOn_of_isIntegralCurveOn_Icc_of_fderiv hGd hD hx
      (isIntegralCurveOn_of_localField
        ((flow_solution hGlc hK _ _).mono Icc_subset_Ici_self)
        fun u hu => hRnear u _ (hnear u hu))
      (flow_start hGlc hK _ _).symm
  -- from within `δ₁` the localized flow stays within `1` of `x_*`
  obtain ⟨δ₁, hδ₁, hb₁⟩ := hstab 1 one_pos
  have hnear : ∀ τ (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ₁ → ∀ u, τ ≤ u →
      ‖flow hGlc hK τ ξ u - xs u‖ < 1 := fun τ ξ hξ u hu =>
    hb₁ τ _ (flow_solution hGlc hK τ ξ) (by rwa [flow_start]) u hu
  refine ⟨fun ε hε => ?_, min δa δ₁, lt_min hδa hδ₁, fun τ ξ hξ => ?_, fun ε hε => ?_⟩
  · -- uniform Lyapunov stability
    obtain ⟨δ, hδ, hb⟩ := hstab (min ε 1) (lt_min hε one_pos)
    refine ⟨δ, hδ, fun τ t x hτt hx hx0 => ?_⟩
    have hfl : ∀ u, τ ≤ u → ‖flow hGlc hK τ (x τ) u - xs u‖ < min ε 1 := fun u hu =>
      hb τ _ (flow_solution hGlc hK τ (x τ)) (by rwa [flow_start]) u hu
    rw [heqOn hx (fun u hu => ((hfl u hu.1).trans_le (min_le_right _ _)).le) ⟨hτt, le_rfl⟩]
    exact (hfl t hτt).trans_le (min_le_left _ _)
  · -- existence on `[τ, ∞)`
    exact ⟨flow hGlc hK τ ξ, flow_start hGlc hK τ ξ,
      isIntegralCurveOn_of_localField (flow_solution hGlc hK τ ξ) fun u hu =>
        hRnear u _ (hnear τ ξ (hξ.trans_le (min_le_right _ _)) u hu).le⟩
  · -- uniform attraction
    obtain ⟨S, hS0, hS⟩ := hatt ε hε
    refine ⟨S, hS0, fun τ t x hτt hx hx0 => ?_⟩
    have hx0' : ‖flow hGlc hK τ (x τ) τ - xs τ‖ < δa := by
      rw [flow_start]; exact hx0.trans_le (min_le_left _ _)
    rw [heqOn hx (fun u hu => (hnear τ (x τ) (hx0.trans_le (min_le_right _ _)) u hu.1).le)
      ⟨by linarith, le_rfl⟩]
    exact hS τ _ (flow_solution hGlc hK τ (x τ)) hx0' t hτt

/-- **From the localized period map to the solutions of `G`: instability.** For a `T`-periodic
field `G`, a solution `x_*` with `x_*(T) = x_*(0)` and a radius `R` with `‖y‖ ≤ R` whenever
`‖y − x_*(t)‖ ≤ 1`, with `G̃ = localField G R` continuous and `K`-Lipschitz (no regularity of
`G` is needed here): if the period map of `G̃` (read on `ℝⁿ`) is unstable at `x_*(0)`, then
`x_*` is an unstable solution of `G` with one escape radius for every initial time: there is
`ε > 0` such that for every `τ` and every `δ > 0` a solution of `G` on a segment `[τ, t]` starts
within `δ` of `x_*(τ)` and ends at the distance at least `ε` from `x_*(t)`
(`FlipOrbitUniform.uniformlyUnstable_of_map` for `G̃`, cut at the first exit from the tube of
radius `1`, inside which it solves `G`). -/
@[tmio T, powerlib_foundation] theorem uniformlyUnstable_local_of_map
    {R : ℝ} {K : NNReal}
    (hGlc : Continuous (uncurry (localField G R))) (hK : ∀ t, LipschitzWith K (localField G R t))
    {T : ℝ} (hT : 0 < T) (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ R)
    (h : Map.Unstable (euclidMap (periodMap hGlc hK T))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    ∃ ε, 0 < ε ∧ ∀ (τ δ : ℝ), 0 < δ → ∃ (x : ℝ → Fin n → ℝ) (t : ℝ), τ ≤ t ∧
      IsIntegralCurveOn x G (Icc τ t) ∧ ‖x τ - xs τ‖ < δ ∧ ε ≤ ‖x t - xs t‖ := by
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRnear t (xs t) (by simp))]; exact hxs t
  obtain ⟨ε₀, hε₀, hesc⟩ :=
    uniformlyUnstable_of_map hGlc hK hT (periodic_localField hGper R) hxsl hfix h
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun τ δ hδ => ?_⟩
  obtain ⟨y, hy, hy0, t₁, ht₁, hyt₁⟩ :=
    hesc (min δ (min ε₀ 1)) (lt_min hδ (lt_min hε₀ one_pos)) τ
  -- the first time the escaping solution reaches the distance `min ε₀ 1`; until then it is in
  -- the tube of radius `1`, where it solves `G`
  have hfirst : ∃ s ∈ Icc τ t₁, (∀ u ∈ Icc τ s, ‖y u - xs u‖ ≤ 1) ∧
      min ε₀ 1 ≤ ‖y s - xs s‖ := by
    by_contra hcon
    push Not at hcon
    have hc := Dynamics.forall_lt_of_first_exit (φ := fun u => y u - xs u) (Φ := norm)
      (c := min ε₀ 1) continuous_norm
      ((hy.continuousOn.mono Icc_subset_Ici_self).sub hxsc.continuousOn)
      (hy0.trans_le (min_le_right _ _))
      (fun s hs hle => hcon s hs fun u hu => (hle u hu).trans (min_le_right _ _)) t₁
      ⟨ht₁, le_rfl⟩
    exact absurd hyt₁ (not_le.2 (hc.trans_le (min_le_left _ _)))
  obtain ⟨s, hs, hle, hesc'⟩ := hfirst
  exact ⟨y, s, hs.1, isIntegralCurveOn_of_localField (hy.mono Icc_subset_Ici_self)
    fun u hu => hRnear u _ (hle u hu), hy0.trans_le (min_le_left _ _), hesc'⟩

/-- **The degenerate flip of a periodic solution of a locally Lipschitz field, stable side.**
Let `G` be `T`-periodic in `t`, continuous, differentiable in `x` with `D_xG` jointly continuous
(no Lipschitz bound), `x_*` a global solution with `x_*(T) = x_*(0)`, with the fifth-order
expansion along `x_*` and the spectral, coefficient and homological data of
`orbit_stable_of_degenerateFlip`. If `c₂² + c₃ = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ > 0`, then:
* the period map of `G` near `x_*(0)` — a map `P` with `x(T) = P(x(0))` for the solutions of `G`
  on `[0, T]` starting within `r` of `x_*(0)`, which exist — is locally asymptotically, not
  exponentially, stable at `x_*(0)` (read on `ℝⁿ`);
* `x_*` is uniformly Lyapunov stable: for every `ε` one `δ` serves every initial time `τ` and
  every solution on a segment `[τ, t]`;
* from within some `δ` of `x_*(τ)` the solutions exist on `[τ, ∞)` and are uniformly attracted.
The proof localizes `G` by `LocalField.localField` with a radius beyond the orbit and the tube of
the expansion, where the jet, the monodromy and the verdict are those of `G`. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_degenerateFlip_local
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0) {Q : ℝ → FormalMultilinearSeries ℝ (Fin n → ℝ) (Fin n → ℝ)}
    (hQ : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => Q r k) {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) Q 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) Q 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) Q 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) Q 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : 0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.LocalAsymptoticStable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap P)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ ≤ t →
      IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ (∀ (τ : ℝ) (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ →
        ∃ x : ℝ → Fin n → ℝ, x τ = ξ ∧ IsIntegralCurveOn x G (Ici τ)) ∧
      ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ + S ≤ t →
        IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε := by
  have hxsp := periodic_of_fixed_of_fderiv hGd hD hGper hxs hfix
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  -- a ball of radius `R` containing the tube `‖u‖ ≤ ρ` (strictly) and the tube of radius `1`
  obtain ⟨Bx, hBx⟩ := isBounded_iff_forall_norm_le.1
    (hxsp.compact_of_continuous hT.ne' hxsc).isBounded
  have hRtube : ∀ t (u : Fin n → ℝ), ‖u‖ ≤ ρ → ‖xs t + u‖ < Bx + ρ + 1 := fun t u hu => by
    have := hBx (xs t) (mem_range_self t)
    calc ‖xs t + u‖ ≤ ‖xs t‖ + ‖u‖ := norm_add_le _ _
      _ < Bx + ρ + 1 := by linarith
  have hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ Bx + ρ + 1 := fun t y hy => by
    have := hBx (xs t) (mem_range_self t)
    calc ‖y‖ = ‖xs t + (y - xs t)‖ := by rw [add_sub_cancel]
      _ ≤ ‖xs t‖ + ‖y - xs t‖ := norm_add_le _ _
      _ ≤ Bx + ρ + 1 := by linarith
  set R := Bx + ρ + 1 with hR
  have hRxs : ∀ t, ‖xs t‖ < R := fun t => by simpa using hRtube t 0 (by simp [hρ.le])
  obtain ⟨K, hK⟩ := exists_lipschitzWith_localField hGd hD hT hGper R
  have hGlc := continuous_localField hGc R
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRxs t).le]; exact hxs t
  have hjac : jacobianAlong (localField G R) xs = jacobianAlong G xs := funext fun t => by
    unfold jacobianAlong; rw [fderiv_localField_eq (hRxs t)]
  have hTayl : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖localField G R r (xs r + u) -
      localField G R r (xs r) - fderiv ℝ (localField G R r) (xs r) u -
        ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6 := fun r hr u hu => by
    rw [localField_eq (hRtube r u hu).le, localField_eq (hRxs r).le,
      fderiv_localField_eq (hRxs r)]
    exact hTay r hr u hu
  rw [← hjac] at hv hw hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hk₄
  obtain ⟨r, hr, hex, hPl⟩ := periodMap_localField hGd hD hGlc hK hT.le hxs hRnear
  obtain ⟨hmap, -⟩ := orbit_stable_of_degenerateFlip hGlc (differentiableAt_localField hGd R)
    (continuous_fderiv_localField hGd hD R) hK hT (periodic_localField hGper R) hxsl hfix hQ hρ
    hTayl hv hw hwv hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hwk₃ hk₄ hdeg hκ
  exact ⟨⟨periodMap hGlc hK T, r, hr, hex, hPl, hmap⟩,
    uniformlyStable_local_of_map hGd hD hGlc hK hT hGper hxs hfix hRnear hmap.1⟩

/-- **The degenerate flip of a periodic solution of a locally Lipschitz field, unstable side.**
Under the hypotheses of `orbit_stable_of_degenerateFlip_local`, if `c₂² + c₃ = 0` and
`c₅ + 3c₂c₄ − 2c₂⁴ < 0`, the period map of `G` near `x_*(0)` is unstable and `x_*` is unstable
with one escape radius for every initial time (escaping solutions on segments `[τ, t]`). -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_degenerateFlip_local
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0) {Q : ℝ → FormalMultilinearSeries ℝ (Fin n → ℝ) (Fin n → ℝ)}
    (hQ : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => Q r k) {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) Q 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) Q 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) Q 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) Q 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.Unstable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    ∃ ε, 0 < ε ∧ ∀ (τ δ : ℝ), 0 < δ → ∃ (x : ℝ → Fin n → ℝ) (t : ℝ), τ ≤ t ∧
      IsIntegralCurveOn x G (Icc τ t) ∧ ‖x τ - xs τ‖ < δ ∧ ε ≤ ‖x t - xs t‖ := by
  have hxsp := periodic_of_fixed_of_fderiv hGd hD hGper hxs hfix
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  -- a ball of radius `R` containing the tube `‖u‖ ≤ ρ` (strictly) and the tube of radius `1`
  obtain ⟨Bx, hBx⟩ := isBounded_iff_forall_norm_le.1
    (hxsp.compact_of_continuous hT.ne' hxsc).isBounded
  have hRtube : ∀ t (u : Fin n → ℝ), ‖u‖ ≤ ρ → ‖xs t + u‖ < Bx + ρ + 1 := fun t u hu => by
    have := hBx (xs t) (mem_range_self t)
    calc ‖xs t + u‖ ≤ ‖xs t‖ + ‖u‖ := norm_add_le _ _
      _ < Bx + ρ + 1 := by linarith
  have hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ Bx + ρ + 1 := fun t y hy => by
    have := hBx (xs t) (mem_range_self t)
    calc ‖y‖ = ‖xs t + (y - xs t)‖ := by rw [add_sub_cancel]
      _ ≤ ‖xs t‖ + ‖y - xs t‖ := norm_add_le _ _
      _ ≤ Bx + ρ + 1 := by linarith
  set R := Bx + ρ + 1 with hR
  have hRxs : ∀ t, ‖xs t‖ < R := fun t => by simpa using hRtube t 0 (by simp [hρ.le])
  obtain ⟨K, hK⟩ := exists_lipschitzWith_localField hGd hD hT hGper R
  have hGlc := continuous_localField hGc R
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRxs t).le]; exact hxs t
  have hjac : jacobianAlong (localField G R) xs = jacobianAlong G xs := funext fun t => by
    unfold jacobianAlong; rw [fderiv_localField_eq (hRxs t)]
  have hTayl : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖localField G R r (xs r + u) -
      localField G R r (xs r) - fderiv ℝ (localField G R r) (xs r) u -
        ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6 := fun r hr u hu => by
    rw [localField_eq (hRtube r u hu).le, localField_eq (hRxs r).le,
      fderiv_localField_eq (hRxs r)]
    exact hTay r hr u hu
  rw [← hjac] at hv hw hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hk₄
  obtain ⟨r, hr, hex, hPl⟩ := periodMap_localField hGd hD hGlc hK hT.le hxs hRnear
  obtain ⟨hmap, -⟩ := orbit_unstable_of_degenerateFlip hGlc (differentiableAt_localField hGd R)
    (continuous_fderiv_localField hGd hD R) hK hT (periodic_localField hGper R) hxsl hfix hQ hρ
    hTayl hv hw hwv hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hwk₃ hk₄ hdeg hκ
  exact ⟨⟨periodMap hGlc hK T, r, hr, hex, hPl, hmap⟩,
    uniformlyUnstable_local_of_map hGlc hK hT hGper hxs hfix hRnear hmap⟩

/-- **Fields of class `C⁶` without a global Lipschitz bound, stable side.**
`orbit_stable_of_degenerateFlip_local` for a field with `G(t, ·)` of class `C⁶`, `D_x^kG`
continuous along `x_*` for `2 ≤ k ≤ 5` and `‖D_x⁶G‖ ≤ B` on the tube of radius `ρ` about `x_*`,
with `Q_k = D_x^kG/k!` along `x_*` (`PeriodMapJet.taylorSeries`). -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_degenerateFlip_of_contDiff_local
    (hGc : Continuous (uncurry G)) (hG6 : ∀ t, ContDiff ℝ 6 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0)
    (hDk : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => iteratedFDeriv ℝ k (G r) (xs r))
    {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 6 (G r) y‖ ≤ B)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : 0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.LocalAsymptoticStable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap P)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ ≤ t →
      IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ (∀ (τ : ℝ) (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ →
        ∃ x : ℝ → Fin n → ℝ, x τ = ξ ∧ IsIntegralCurveOn x G (Ici τ)) ∧
      ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ + S ≤ t →
        IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε :=
  orbit_stable_of_degenerateFlip_local hGc (fun t => (hG6 t).differentiable (by norm_num)) hD hT
    hGper hxs hfix (fun k hk1 hk2 => (hDk k hk1 hk2).const_smul ((k.factorial : ℝ)⁻¹)) hρ
    (taylor_along_of_contDiff_order (by norm_num) (fun r _ y _ => (hG6 r).contDiffAt) hB)
    hv hw hwv hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hwk₃ hk₄ hdeg hκ

/-- **Fields of class `C⁶` without a global Lipschitz bound, unstable side.**
`orbit_unstable_of_degenerateFlip_local` with `Q_k = D_x^kG/k!` along `x_*`, under the
hypotheses of `orbit_stable_of_degenerateFlip_of_contDiff_local`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_degenerateFlip_of_contDiff_local
    (hGc : Continuous (uncurry G)) (hG6 : ∀ t, ContDiff ℝ 6 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0)
    (hDk : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => iteratedFDeriv ℝ k (G r) (xs r))
    {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 6 (G r) y‖ ≤ B)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) (taylorSeries G xs) 0 T 5)
    {k₂ k₃ k₄ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hk₃ : -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
      curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
        (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂)
    (hwk₃ : wm ⬝ᵥ k₃ = 0)
    (hk₄ : k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ = curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
      (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
      ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
      (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃)
    (hdeg : (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0)
    (hκ : wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
      3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) - 2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.Unstable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    ∃ ε, 0 < ε ∧ ∀ (τ δ : ℝ), 0 < δ → ∃ (x : ℝ → Fin n → ℝ) (t : ℝ), τ ≤ t ∧
      IsIntegralCurveOn x G (Icc τ t) ∧ ‖x τ - xs τ‖ < δ ∧ ε ≤ ‖x t - xs t‖ :=
  orbit_unstable_of_degenerateFlip_local hGc (fun t => (hG6 t).differentiable (by norm_num)) hD
    hT hGper hxs hfix (fun k hk1 hk2 => (hDk k hk1 hk2).const_smul ((k.factorial : ℝ)⁻¹)) hρ
    (taylor_along_of_contDiff_order (by norm_num) (fun r _ y _ => (hG6 r).contDiffAt) hB)
    hv hw hwv hS hP₂ hP₃ hP₄ hP₅ hk₂ hk₃ hwk₃ hk₄ hdeg hκ

end Local

end powerlib.Periodic.DegenerateFlipOrbit
