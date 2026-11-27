import theorem.Periodic.FlipReduction
import theorem.Periodic.PeriodMapTaylor

/-! # The flip reduction of a periodic solution, with the period map derived from the field

`theorem/Periodic/FlipReduction.lean` decides a fixed point with a simple multiplier `−1` and a
stable complement by the flip coefficient `a² + b`, for a map whose strict derivative and cubic
Taylor expansion are hypotheses. Here the map is the period map `P(ξ) = x(T; 0, ξ)` of a
`T`-periodic system `ẋ = G(t, x)` at a `T`-periodic solution `x_*`, and these hypotheses are
derived from the field: `P(x_*(0)) = x_*(0)` (`FlowDerivative.periodMap_fixed`),
`DP(x_*(0)) = Φ(T, 0)`, the monodromy of the variational equation along `x_*`
(`FlowDerivative.hasStrictFDerivAt_periodMap`), and
`P(p + e) = p + Φ(T, 0) e + P₂(e, e) + P₃(e, e, e) + O(‖e‖⁴)` with the second and third
variations `P₂, P₃` of `theorem/Periodic/PeriodMapTaylor.lean` (`periodMap_taylor`). The flip
coefficient is therefore expressed in the variational data of the orbit:
`a = wᵀ P₂(v, v)`, `b = wᵀ P₃(v, v, v) + wᵀ (P₂(v, k) + P₂(k, v))`,
`(I − M) k = P₂(v, v) − (wᵀ P₂(v, v)) v`, with `M v = −v`, `wᵀ M = −wᵀ`, `wᵀ v = 1`. A positive
flip coefficient makes the period map locally asymptotically (not exponentially) stable and the
periodic solution Lyapunov stable and attracting; a negative one makes both unstable.

The step from the period map to the solutions: for a `T`-periodic field every solution on
`[0, ∞)` satisfies `x(kT) = Pᵏ(x(0))` (uniqueness of solutions and periodicity of `G`), and on each
period `‖x(t) − x_*(t)‖ ≤ e^{KT} ‖P^{⌊t/T⌋}(x(0)) − x_*(0)‖` (Grönwall).

Scope.
* The solutions live in `ℝ^{Fin n}` with the sup norm (`theorem/Periodic/Transition.lean`); the map
  semantics (`Map.LocalAsymptoticStable`, `Map.LocallyExponentiallyStable`, `Map.Unstable`) is on
  `ℝⁿ = EuclideanSpace ℝ (Fin n)`, and a map of `Fin n → ℝ` is read there through the coordinate
  isomorphism `EuclideanSpace.equiv` (`euclidMap`); the conversions only use its operator norms.
* `G` is `T`-periodic in `t` (`Function.Periodic G T`, `T > 0`), continuous, differentiable in `x`
  with `D_xG` jointly continuous, and globally `K`-Lipschitz in `x` (a field that is only locally
  Lipschitz is first multiplied by a smooth cut-off equal to `1` near the orbit, which is not done
  here; it is done in `theorem/Periodic/LocalField.lean`, `orbit_stable_of_flipCoeff_pos_local`,
  `orbit_unstable_of_flipCoeff_neg_local`). `x_*` is a global solution with `x_*(T) = x_*(0)`.
* Along `x_*` on `[0, T]` the field has the cubic Taylor expansion with continuous coefficients
  `D_xG(r, x_*(r))`, `Q₂(r)`, `Q₃(r)` and a remainder `c₄ ‖u‖⁴` for `‖u‖ ≤ ρ`
  (`PeriodMapTaylor`); for a field of class `C⁴` in `x` with `D_x²G`, `D_x³G` continuous along
  `x_*` and `‖D_x⁴G‖` bounded on the tube it holds with `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` (the
  `_of_contDiff` theorems). The bounds of `Q₂`, `Q₃` on `[0, T]` come from their continuity.
* The spectral hypothesis is the projector form of `FlipReduction.multipliers_of_deflate` for the
  monodromy matrix `M = monodromy (jacobianAlong G x_*) T 0`: `M vm = −vm`, `wmᵀ M = −wmᵀ`,
  `wm ⬝ vm = 1`, `M + vm wmᵀ` Schur stable (`−1` simple, every other multiplier strictly inside the
  unit circle).
* The solution statements concern the initial time `0` (solutions on `[0, ∞)`; uniformly in the
  initial time: `theorem/Periodic/FlipOrbitUniform.lean`); the degenerate flip `a² + b = 0` is not
  decided here (from the fifth-order jet of the field: `theorem/Periodic/DegenerateFlipOrbit.lean`).
* Only the multiplier `−1` is reduced here. A periodic solution with the multiplier `+1` (the
  transcritical and cubic normal forms of `theorem/Periodic/CriticalMultiplier.lean`) is
  `theorem/Periodic/FoldOrbit.lean`, with the reduction at `+1` in
  `theorem/Periodic/FoldReduction.lean`.
* Generic mathematics; no model family.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), Ch. 4 (the flip bifurcation
of fixed points of maps) and §5.4 (the Poincaré map of a periodic orbit, its derivative the
monodromy matrix, its Taylor coefficients from the variational equations); the open items of
`theorem/Periodic/FlipReduction.lean` (Scope: the regularity of the period map and
`DP(x_*(0)) = Φ(T, 0)` were hypotheses there), discharged with
`theorem/Periodic/FlowDerivative.lean` and `theorem/Periodic/PeriodMapTaylor.lean`.

Results.
* `euclidMap`, `iterate_euclidMap`, `dotCLM`, `dotCLM_apply` — maps and functionals of
  `Fin n → ℝ` read on `ℝⁿ`.
* `localAsymptoticStable_of_flipCoeff_pos_coord`, `unstable_of_flipCoeff_neg_coord` — the flip
  reduction (`FlipReduction.localAsymptoticStable_of_flipCoeff_pos_matrix`,
  `FlipReduction.unstable_of_flipCoeff_neg_matrix`) for a map of `Fin n → ℝ` with matrix data.
* `exists_bound_bilin` — a continuous family of bilinear maps is bounded on a compact interval.
* `iterate_periodMap`, `solution_nat_mul_period`, `norm_sub_le_iterate` — the solutions sampled
  at the periods are the iterates of the period map; the deviation between the periods.
* `solution_stable_of_map`, `solution_unstable_of_map` — stability and instability of the period
  map give those of the periodic solution.
* **The theorems**: `orbit_stable_of_flipCoeff_pos` (`a² + b > 0`: the period map is locally
  asymptotically, not exponentially, stable at `x_*(0)`, and `x_*` is Lyapunov stable and
  attracting) and `orbit_unstable_of_flipCoeff_neg` (`a² + b < 0`: the period map and `x_*` are
  unstable); `orbit_stable_of_flipCoeff_pos_of_contDiff`,
  `orbit_unstable_of_flipCoeff_neg_of_contDiff` — the same for a field of class `C⁴` in `x`, with
  `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` along `x_*` and the remainder from a bound on `D_x⁴G`.

Corrections.
None: an extension (`FlipReduction` for the period map of a periodic system, with its regularity
derived from the field).

Family and connection conclusions.
None: static evidence on periodic ODEs (stability of a periodic solution at a period-doubling
multiplier).
-/

noncomputable section
namespace powerlib.Periodic.FlipOrbit

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Maps on `Fin n → ℝ` read on `ℝⁿ` -/

/-- A map of `Fin n → ℝ` (sup norm) read on the Euclidean state space `ℝⁿ` of the map semantics,
through the coordinate isomorphism `EuclideanSpace.equiv`. -/
def euclidMap (F : (Fin n → ℝ) → Fin n → ℝ) : ℝⁿ → ℝⁿ :=
  fun y => (EuclideanSpace.equiv (Fin n) ℝ).symm (F (EuclideanSpace.equiv (Fin n) ℝ y))

@[tmio T, powerlib_foundation] theorem iterate_euclidMap (F : (Fin n → ℝ) → Fin n → ℝ) (k : ℕ)
    (y : ℝⁿ) :
    (euclidMap F)^[k] y =
      (EuclideanSpace.equiv (Fin n) ℝ).symm (F^[k] (EuclideanSpace.equiv (Fin n) ℝ y)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', euclidMap,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The linear functional `e ↦ w ⬝ᵥ e` on `Fin n → ℝ`. -/
def dotCLM (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => w ⬝ᵥ e
      map_add' := dotProduct_add w
      map_smul' := fun c e => dotProduct_smul c w e }

@[tmio T, powerlib_foundation] theorem dotCLM_apply (w e : Fin n → ℝ) : dotCLM w e = w ⬝ᵥ e := rfl

/-- **The flip data in Euclidean coordinates.** The hypotheses of the matrix forms of
`FlipReduction` for `euclidMap F`, from a strict derivative `Mm`, the projector data
`Mm vm = −vm`, `wmᵀ Mm = −wmᵀ`, `wm ⬝ vm = 1`, a cubic Taylor expansion and a solution `k` of
`k − Mm k = Q P₂(vm, vm)`, all in the coordinates `Fin n → ℝ` (sup norm). -/
@[tmio T, powerlib_foundation] private theorem flip_coords {F : (Fin n → ℝ) → Fin n → ℝ}
    {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm) :
    ∃ (vE : ℝⁿ) (wE : ℝⁿ →L[ℝ] ℝ) (P₂E : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ)
      (P₃E : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ℝⁿ) ℝⁿ) (kE : ℝⁿ) (ρ C' : ℝ),
      0 < ρ ∧
      HasStrictFDerivAt (euclidMap F) (Linear.op Mm) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) ∧
      euclidMap F ((EuclideanSpace.equiv (Fin n) ℝ).symm p) =
        (EuclideanSpace.equiv (Fin n) ℝ).symm p ∧
      Linear.op Mm vE = -vE ∧ (∀ e, wE (Linear.op Mm e) = -wE e) ∧ wE vE = 1 ∧
      Linear.op (Mm + vecMulVec vm wm) = FlipReduction.deflate (Linear.op Mm) vE wE ∧
      (∀ e, ‖e‖ ≤ ρ → ‖euclidMap F ((EuclideanSpace.equiv (Fin n) ℝ).symm p + e) -
        (EuclideanSpace.equiv (Fin n) ℝ).symm p - Linear.op Mm e - P₂E e e -
          P₃E (fun _ => e)‖ ≤ C' * ‖e‖ ^ 4) ∧
      kE - Linear.op Mm kE = FlipReduction.specProj vE wE (P₂E vE vE) ∧
      wE (P₂E vE vE) = wm ⬝ᵥ P₂ vm vm ∧
      wE (P₃E (fun _ => vE)) + wE (P₂E vE kE + P₂E kE vE) =
        wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm) := by
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (ε : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  set P₂E : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ :=
    ((ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝⁿ εS).comp P₂).bilinearComp εL εL
    with hP₂E
  set P₃E : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ℝⁿ) ℝⁿ :=
    εS.compContinuousMultilinearMap (P₃.compContinuousLinearMap fun _ => εL) with hP₃E
  have hP₂Ea : ∀ a b, P₂E a b = ε.symm (P₂ (ε a) (ε b)) := fun a b => by
    simp [hP₂E, hεS, hεL]
  have hP₃Ea : ∀ a, P₃E (fun _ => a) = ε.symm (P₃ (fun _ => ε a)) := fun a => by
    simp [hP₃E, hεS, hεL]
  have hop : ∀ y, Linear.op Mm y = ε.symm (Mm *ᵥ ε y) := fun y => rfl
  set wE : ℝⁿ →L[ℝ] ℝ := (dotCLM wm).comp εL with hwE
  have hwEa : ∀ y, wE y = wm ⬝ᵥ ε y := fun y => rfl
  refine ⟨ε.symm vm, wE, P₂E, P₃E, ε.symm k, ρ₀ / (‖εL‖ + 1), ‖εS‖ * C * ‖εL‖ ^ 4,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the strict derivative
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
  · show ε.symm (F (ε (ε.symm p))) = ε.symm p
    rw [ContinuousLinearEquiv.apply_symm_apply, hFp]
  · rw [hop, ContinuousLinearEquiv.apply_symm_apply, hv, map_neg]
  · intro e
    rw [hwEa, hwEa, hop, ContinuousLinearEquiv.apply_symm_apply, Matrix.dotProduct_mulVec, hw,
      neg_dotProduct]
  · rw [hwEa, ContinuousLinearEquiv.apply_symm_apply, hwv]
  · ext1 y
    rw [FlipReduction.deflate_apply, hop, hwEa]
    show ε.symm ((Mm + vecMulVec vm wm) *ᵥ ε y) = _
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, map_add, op_smul_eq_smul, map_smul]
  · intro e he
    have hεe : ‖ε e‖ ≤ ρ₀ := by
      have h1 : ‖ε e‖ ≤ ‖εL‖ * ‖e‖ := εL.le_opNorm e
      have h2 : ‖εL‖ * ‖e‖ ≤ (‖εL‖ + 1) * ‖e‖ := by nlinarith [norm_nonneg e]
      have h3 : (‖εL‖ + 1) * ‖e‖ ≤ ρ₀ := by
        rw [le_div_iff₀ (by positivity)] at he; linarith
      linarith
    have hid : euclidMap F (ε.symm p + e) - ε.symm p - Linear.op Mm e - P₂E e e -
        P₃E (fun _ => e) = ε.symm (F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) -
          P₃ (fun _ => ε e)) := by
      have hE : euclidMap F (ε.symm p + e) = ε.symm (F (p + ε e)) := by
        show ε.symm (F (ε (ε.symm p + e))) = _
        rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
      rw [hE, hP₂Ea, hP₃Ea, hop]
      simp only [map_sub]
    rw [hid]
    calc ‖ε.symm (F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) - P₃ (fun _ => ε e))‖
        ≤ ‖εS‖ * ‖F (p + ε e) - p - Mm *ᵥ ε e - P₂ (ε e) (ε e) - P₃ (fun _ => ε e)‖ :=
          εS.le_opNorm _
      _ ≤ ‖εS‖ * (C * ‖ε e‖ ^ 4) := by gcongr; exact hTay _ hεe
      _ ≤ ‖εS‖ * (C * (‖εL‖ * ‖e‖) ^ 4) := by gcongr; exact εL.le_opNorm e
      _ = ‖εS‖ * C * ‖εL‖ ^ 4 * ‖e‖ ^ 4 := by ring
  · rw [hop, FlipReduction.specProj_apply, hwEa, hP₂Ea]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [← map_sub, hk, map_sub, map_smul]
  · rw [hwEa, hP₂Ea, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  · rw [hwEa, hwEa, hP₃Ea, hP₂Ea, hP₂Ea, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, ← map_add, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]

/-- **The flip reduction in the coordinates `Fin n → ℝ`, stable side.** A map `F` of
`Fin n → ℝ` with fixed point `p`, strict derivative `Mm` there, the projector data of a simple
multiplier `−1` with Schur stable deflation `Mm + vm wmᵀ` (`FlipReduction.multipliers_of_deflate`),
the cubic expansion `‖F(p + e) − p − Mm e − P₂(e, e) − P₃(e, e, e)‖ ≤ C ‖e‖⁴` on `‖e‖ ≤ ρ₀` and a
solution `k` of `k − Mm k = P₂(vm, vm) − (wm ⬝ P₂(vm, vm)) vm`: if the flip coefficient
`a² + b`, `a = wm ⬝ P₂(vm, vm)`, `b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))`, is
positive, then `F` read on `ℝⁿ` is locally asymptotically, not exponentially, stable at `p`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_flipCoeff_pos_coord
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ P₂ vm vm) ^ 2 + (wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm))) :
    Map.LocalAsymptoticStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) := by
  obtain ⟨vE, wE, P₂E, P₃E, kE, ρ, C', hρ, hP, hPp, hv', hw', hwv', hL, hTay', hk', ha, hb⟩ :=
    flip_coords hF hFp hv hw hwv hC hρ₀ hTay hk
  exact FlipReduction.localAsymptoticStable_of_flipCoeff_pos_matrix hP hPp hv' hw' hwv' hL hS hρ
    hTay' hk' (by rw [ha, hb]; exact hab)

/-- **The flip reduction in the coordinates `Fin n → ℝ`, unstable side.** Under the hypotheses of
`localAsymptoticStable_of_flipCoeff_pos_coord`, a negative flip coefficient `a² + b` makes `F`
read on `ℝⁿ` unstable at `p`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_flipCoeff_neg_coord
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hab : (wm ⬝ᵥ P₂ vm vm) ^ 2 + (wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm)) < 0) :
    Map.Unstable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) := by
  obtain ⟨vE, wE, P₂E, P₃E, kE, ρ, C', hρ, hP, hPp, hv', hw', hwv', hL, hTay', hk', ha, hb⟩ :=
    flip_coords hF hFp hv hw hwv hC hρ₀ hTay hk
  exact FlipReduction.unstable_of_flipCoeff_neg_matrix hP hPp hv' hw' hwv' hL hS hρ
    hTay' hk' (by rw [ha, hb]; exact hab)

/-! ## From the period map to the solutions of the periodic system -/

section Orbit

variable {G : ℝ → (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

/-- **Sampling at the periods.** For a `T`-periodic field every solution on `[0, ∞)` satisfies
`x(kT) = Pᵏ(x(0))`, `P` the period map. -/
@[tmio T, powerlib_foundation] theorem iterate_periodMap (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 ≤ T) (hGper : Periodic G T)
    {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x G (Ici 0)) (k : ℕ) :
    x (k * T) = (periodMap hGc hK T)^[k] (x 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    set y : ℝ → Fin n → ℝ := fun r => x (r + k * T) with hydef
    have hkT : 0 ≤ (k : ℝ) * T := mul_nonneg (Nat.cast_nonneg k) hT
    have hy : IsIntegralCurveOn y G (Icc 0 T) := by
      intro r hr
      have hmaps : MapsTo (fun r : ℝ => r + k * T) (Icc 0 T) (Ici 0) := fun q hq => by
        simp only [mem_Ici]; linarith [hq.1]
      have h := HasDerivWithinAt.scomp r (hx (r + k * T) (hmaps hr))
        ((hasDerivAt_id' r).hasDerivWithinAt.add_const ((k : ℝ) * T)) hmaps
      have hG : G (r + k * T) = G r := (hGper.nat_mul k) r
      simpa only [Function.comp_def, one_smul, hG] using h
    have hy0 : y 0 = x (k * T) := by simp [hydef]
    have hyT := flow_eq hGc hK hy0 hy T ⟨hT, le_rfl⟩
    rw [Function.iterate_succ_apply', ← ih]
    have h1 : x ((k + 1 : ℕ) * T) = y T := by
      simp only [hydef]; congr 1; push_cast; ring
    rw [h1, hyT]
    rfl

/-- A solution with `x_*(T) = x_*(0)` of a `T`-periodic system returns to `x_*(0)` at every
period. -/
@[tmio T, powerlib_foundation] theorem solution_nat_mul_period (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 ≤ T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (k : ℕ) : xs (k * T) = xs 0 := by
  rw [iterate_periodMap hGc hK hT hGper (fun r _ => (hxs r).hasDerivWithinAt) k]
  exact Function.iterate_fixed (periodMap_fixed hGc hK hxs hT hfix) k

/-- **The deviation between the periods.** For a `T`-periodic field and a solution `x_*` with
`x_*(T) = x_*(0)`, every solution on `[0, ∞)` satisfies
`‖x(t) − x_*(t)‖ ≤ e^{KT} ‖P^{⌊t/T⌋}(x(0)) − x_*(0)‖` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_le_iterate (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x G (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ‖x t - xs t‖ ≤ Real.exp (K * T) * ‖(periodMap hGc hK T)^[⌊t / T⌋₊] (x 0) - xs 0‖ := by
  set k := ⌊t / T⌋₊ with hk
  set a := (k : ℝ) * T with ha
  have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg k) hT.le
  have hat : a ≤ t := by
    have := Nat.floor_le (div_nonneg ht hT.le)
    rw [← hk] at this
    rw [ha]
    calc (k : ℝ) * T ≤ t / T * T := mul_le_mul_of_nonneg_right this hT.le
      _ = t := by field_simp
  have hta : t < a + T := by
    have := Nat.lt_floor_add_one (t / T)
    rw [← hk] at this
    rw [ha]
    calc t = t / T * T := by field_simp
      _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
      _ = (k : ℝ) * T + T := by ring
  have hxI : IsIntegralCurveOn x G (Icc a (a + T)) := hx.mono fun q hq => le_trans ha0 hq.1
  have hxsI : IsIntegralCurveOn xs G (Icc a (a + T)) := fun r _ => (hxs r).hasDerivWithinAt
  have h := dist_le_of_isIntegralCurveOn_Icc hK hxI hxsI t ⟨hat, hta.le⟩
  rw [dist_eq_norm, dist_eq_norm, iterate_periodMap hGc hK hT.le hGper hx k,
    solution_nat_mul_period hGc hK hT.le hGper hxs hfix k] at h
  refine h.trans ?_
  rw [mul_comm]
  gcongr
  linarith

/-- **From the period map to the solutions: stability.** For a `T`-periodic field and a solution
`x_*` with `x_*(T) = x_*(0)`: if the period map (read on `ℝⁿ`) is locally asymptotically stable
at `x_*(0)`, then `x_*` is Lyapunov stable and attracting from the initial time `0`: solutions on
`[0, ∞)` that start close stay close, and those starting within `δ` converge to `x_*`. -/
@[tmio T, powerlib_foundation] theorem solution_stable_of_map (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (h : Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → Tendsto (fun t => x t - xs t) atTop (𝓝 0) := by
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (E : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (E.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  set P := periodMap hGc hK T with hP
  set pE := E.symm (xs 0) with hpE
  -- the sampled deviation in the two norms
  have hdev : ∀ (ξ : Fin n → ℝ) (j : ℕ),
      P^[j] ξ - xs 0 = E ((euclidMap P)^[j] (E.symm ξ) - pE) := fun ξ j => by
    rw [iterate_euclidMap, map_sub, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hle : ∀ (ξ : Fin n → ℝ) (j : ℕ),
      ‖P^[j] ξ - xs 0‖ ≤ ‖εL‖ * ‖(euclidMap P)^[j] (E.symm ξ) - pE‖ := fun ξ j => by
    rw [hdev]; exact εL.le_opNorm _
  have hstart : ∀ ξ : Fin n → ℝ, ‖E.symm ξ - pE‖ ≤ ‖εS‖ * ‖ξ - xs 0‖ := fun ξ => by
    rw [hpE, ← map_sub]; exact εS.le_opNorm _
  obtain ⟨hLS, c₀, hc₀, hatt⟩ := h
  refine ⟨fun ε hε => ?_, c₀ / (‖εS‖ + 1), by positivity, fun x hx hx0 => ?_⟩
  · set c := Real.exp (K * T) * ‖εL‖ with hc
    have hc0 : 0 ≤ c := by positivity
    obtain ⟨δ₁, hδ₁, hb⟩ := hLS (ε / (c + 1)) (by positivity)
    refine ⟨δ₁ / (‖εS‖ + 1), by positivity, fun x hx hx0 t ht => ?_⟩
    have hy : ‖E.symm (x 0) - pE‖ < δ₁ := by
      refine (hstart _).trans_lt ?_
      rw [lt_div_iff₀ (by positivity)] at hx0
      nlinarith [norm_nonneg εS, norm_nonneg (x 0 - xs 0)]
    have h1 := norm_sub_le_iterate hGc hK hT hGper hxs hfix hx ht
    have h2 := hle (x 0) ⌊t / T⌋₊
    have h3 := hb _ hy ⌊t / T⌋₊
    have h4 : c * (ε / (c + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    calc ‖x t - xs t‖ ≤ Real.exp (K * T) * ‖P^[⌊t / T⌋₊] (x 0) - xs 0‖ := h1
      _ ≤ Real.exp (K * T) * (‖εL‖ *
          ‖(euclidMap P)^[⌊t / T⌋₊] (E.symm (x 0)) - pE‖) := by gcongr
      _ = c * ‖(euclidMap P)^[⌊t / T⌋₊] (E.symm (x 0)) - pE‖ := by rw [hc]; ring
      _ ≤ c * (ε / (c + 1)) := by gcongr
      _ < ε := h4
  · have hy : ‖E.symm (x 0) - pE‖ < c₀ := by
      refine (hstart _).trans_lt ?_
      rw [lt_div_iff₀ (by positivity)] at hx0
      nlinarith [norm_nonneg εS, norm_nonneg (x 0 - xs 0)]
    have hconv : Tendsto (fun j : ℕ => P^[j] (x 0)) atTop (𝓝 (xs 0)) := by
      have h1 := (E.continuous.tendsto pE).comp (hatt _ hy)
      rw [hpE, ContinuousLinearEquiv.apply_symm_apply] at h1
      refine h1.congr fun j => ?_
      simp only [Function.comp_apply, iterate_euclidMap]
      show E (E.symm (P^[j] (E (E.symm (x 0))))) = P^[j] (x 0)
      rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    have hfloor : Tendsto (fun t : ℝ => ⌊t / T⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hT)
    have hg : Tendsto (fun t : ℝ => Real.exp (K * T) * ‖P^[⌊t / T⌋₊] (x 0) - xs 0‖) atTop
        (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 hconv).comp hfloor).const_mul
        (Real.exp (K * T))
      simpa using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hg
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact norm_sub_le_iterate hGc hK hT hGper hxs hfix hx ht

/-- **From the period map to the solutions: instability.** For a `T`-periodic field and a
solution `x_*` with `x_*(T) = x_*(0)`: if the period map (read on `ℝⁿ`) is unstable at `x_*(0)`,
there is `ε > 0` such that solutions on `[0, ∞)` starting arbitrarily close to `x_*(0)` reach the
distance `ε` from `x_*`. -/
@[tmio T, powerlib_foundation] theorem solution_unstable_of_map (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (h : Map.Unstable (euclidMap (periodMap hGc hK T))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (E : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (E.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  set P := periodMap hGc hK T with hP
  set pE := E.symm (xs 0) with hpE
  unfold Map.Unstable Map.LyapunovStable at h
  push Not at h
  obtain ⟨ε₁, hε₁, hesc⟩ := h
  refine ⟨ε₁ / (‖εS‖ + 1), by positivity, fun δ hδ => ?_⟩
  obtain ⟨y, hy, j, hj⟩ := hesc (δ / (‖εL‖ + 1)) (by positivity)
  set x := flow hGc hK 0 (E y) with hx
  have hxI : IsIntegralCurveOn x G (Ici 0) := flow_solution hGc hK 0 _
  have hx0 : x 0 = E y := flow_start hGc hK 0 _
  refine ⟨x, hxI, ?_, j * T, mul_nonneg (Nat.cast_nonneg j) hT.le, ?_⟩
  · rw [hx0, show E y - xs 0 = E (y - pE) by
      rw [map_sub, hpE, ContinuousLinearEquiv.apply_symm_apply]]
    refine (εL.le_opNorm _).trans_lt ?_
    rw [lt_div_iff₀ (by positivity)] at hy
    nlinarith [norm_nonneg εL, norm_nonneg (y - pE)]
  · rw [iterate_periodMap hGc hK hT.le hGper hxI j,
      solution_nat_mul_period hGc hK hT.le hGper hxs hfix j, hx0]
    have h1 : (euclidMap P)^[j] y - pE = E.symm (P^[j] (E y) - xs 0) := by
      rw [iterate_euclidMap, map_sub]
    rw [h1] at hj
    have h2 := hj.trans (εS.le_opNorm _)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (P^[j] (E y) - xs 0)]

/-- A continuous family of bilinear maps on `Fin n → ℝ` is bounded on a compact interval (the
bound from the values on pairs of basis vectors). -/
@[tmio T, powerlib_foundation] theorem exists_bound_bilin
    {Q : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ} (hQ : Continuous Q) (a b : ℝ) :
    ∃ B, ∀ r ∈ Icc a b, ‖Q r‖ ≤ B := by
  have hc : ∀ ij : Fin n × Fin n, ∃ C, ∀ r ∈ Icc a b,
      ‖Q r (Pi.single ij.1 1) (Pi.single ij.2 1)‖ ≤ C := fun ij =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((hQ.clm_apply continuous_const).clm_apply continuous_const).continuousOn
  choose C hC using hc
  refine ⟨∑ ij, max (C ij) 0, fun r hr => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun x y => ?_
  have hexp : Q r x y = ∑ i, ∑ j, (x i * y j) • Q r (Pi.single i 1) (Pi.single j 1) := by
    have := bilinOfBasis_eq (Q r).toLinearMap₁₂ x y
    rw [bilinOfBasis_apply] at this
    exact this.symm
  rw [hexp]
  calc ‖∑ i, ∑ j, (x i * y j) • Q r (Pi.single i 1) (Pi.single j 1)‖
      ≤ ∑ i, ∑ j, ‖(x i * y j) • Q r (Pi.single i 1) (Pi.single j 1)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖x‖ * ‖y‖ * max (C (i, j)) 0 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, norm_mul]
        have h1 := norm_le_pi_norm x i
        have h2 := norm_le_pi_norm y j
        have h3 := (hC (i, j) r hr).trans (le_max_left _ (0 : ℝ))
        have h4 : (0 : ℝ) ≤ max (C (i, j)) 0 := le_max_right _ _
        gcongr
    _ = (∑ ij, max (C ij) 0) * ‖x‖ * ‖y‖ := by
        rw [← Finset.sum_product', Finset.univ_product_univ, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ij _ => by ring

/-- The data of the flip reduction of a periodic solution: the strict derivative, the fixed
point and the cubic expansion of its period map, in the coordinates `Fin n → ℝ`. -/
@[tmio T, powerlib_foundation] private theorem orbit_data (hGc : Continuous (uncurry G))
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4) :
    HasStrictFDerivAt (periodMap hGc hK T)
      (Matrix.toLin' (monodromy (jacobianAlong G xs) T 0)).toContinuousLinearMap (xs 0) ∧
    periodMap hGc hK T (xs 0) = xs 0 ∧
    ∃ C ρ₀ : ℝ, 0 ≤ C ∧ 0 < ρ₀ ∧ ∀ e, ‖e‖ ≤ ρ₀ →
      ‖periodMap hGc hK T (xs 0 + e) - xs 0 - monodromy (jacobianAlong G xs) T 0 *ᵥ e -
        secondVariation (jacobianAlong G xs) Q₂ 0 T e e -
        thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => e)‖ ≤ C * ‖e‖ ^ 4 := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hA := continuous_jacobianAlong hD hxc
  refine ⟨hasStrictFDerivAt_periodMap hGc hGd hD hK hxs hT.le,
    periodMap_fixed hGc hK hxs hT.le hfix, ?_⟩
  have hn₃ : Continuous fun r => ‖Q₃ r‖ := by fun_prop
  obtain ⟨B₂, hB₂⟩ := exists_bound_bilin hQ₂ 0 T
  obtain ⟨B₃, hB₃'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hn₃.continuousOn
  have hB₃ : ∀ r ∈ Icc 0 T, ‖Q₃ r‖ ≤ B₃ := fun r hr => by simpa using hB₃' r hr
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg (Q₂ 0)).trans (hB₂ 0 h0T)
  have hB₃0 : 0 ≤ B₃ := (norm_nonneg (Q₃ 0)).trans (hB₃ 0 h0T)
  have hAK : ∀ r ∈ Icc 0 T, ∀ v, ‖jacobianAlong G xs r *ᵥ v‖ ≤ K * ‖v‖ := fun r _ v => by
    rw [jacobianAlong_mulVec]
    exact ((fderiv ℝ (G r) (xs r)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hK r)) (norm_nonneg v))
  have hTay' : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      jacobianAlong G xs r *ᵥ u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ max c₄ 0 * ‖u‖ ^ 4 :=
    fun r hr u hu => by
      rw [jacobianAlong_mulVec]
      exact (hTay r hr u hu).trans (by gcongr; exact le_max_left _ _)
  refine ⟨taylorConst K T B₂ B₃ (max c₄ 0), min 1 (ρ / Real.exp (K * T)), ?_, by positivity,
    fun e he => periodMap_taylor hGc hK hA hQ₂ hQ₃ hT.le (le_max_right _ _) hAK hB₂ hB₃ hxs hfix
      hTay' e he⟩
  simp only [taylorConst]
  have : 0 ≤ max c₄ 0 := le_max_right _ _
  positivity

/-- **The flip reduction of a periodic solution, stable side.** Let `G` be `T`-periodic in `t`,
continuous, differentiable in `x` with `D_xG` jointly continuous, `K`-Lipschitz in `x`, and let
`x_*` be a solution with `x_*(T) = x_*(0)` along which `G` has the cubic Taylor expansion with
continuous coefficients `D_xG(r, x_*(r))`, `Q₂(r)`, `Q₃(r)` and quartic remainder. Let the
monodromy `M = Φ(T, 0) = monodromy (jacobianAlong G x_*) T 0` have a simple multiplier `−1` with
stable complement in projector form (`M vm = −vm`, `wmᵀ M = −wmᵀ`, `wm ⬝ vm = 1`, `M + vm wmᵀ`
Schur stable), `P₂ = P₂(T)`, `P₃ = P₃(T)` the second and third variations and
`k − M k = P₂(vm, vm) − (wm ⬝ P₂(vm, vm)) vm`. If the flip coefficient
`a² + b`, `a = wm ⬝ P₂(vm, vm)`, `b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))`, is
positive, then the period map (read on `ℝⁿ`) is locally asymptotically, not exponentially, stable
at `x_*(0)`, and `x_*` is a Lyapunov stable and attracting solution: solutions on `[0, ∞)` that
start close to `x_*(0)` stay close to `x_*`, and those starting within some `δ` converge to it. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_flipCoeff_pos
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm))) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → Tendsto (fun t => x t - xs t) atTop (𝓝 0) := by
  obtain ⟨hP, hPp, C, ρ₀, hC, hρ₀, hTay'⟩ :=
    orbit_data hGc hGd hD hK hT hxs hfix hQ₂ hQ₃ hρ hTay
  have hmap := localAsymptoticStable_of_flipCoeff_pos_coord hP hPp hv hw hwv hS hC hρ₀ hTay' hk
    hab
  exact ⟨hmap, solution_stable_of_map hGc hK hT hGper hxs hfix hmap.1⟩

/-- **The flip reduction of a periodic solution, unstable side.** Under the hypotheses of
`orbit_stable_of_flipCoeff_pos`, a negative flip coefficient `a² + b` makes the period map (read
on `ℝⁿ`) unstable at `x_*(0)` and `x_*` an unstable solution: there is `ε > 0` such that solutions
on `[0, ∞)` starting arbitrarily close to `x_*(0)` reach the distance `ε` from `x_*`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_flipCoeff_neg
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (hab : (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm)) < 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  obtain ⟨hP, hPp, C, ρ₀, hC, hρ₀, hTay'⟩ :=
    orbit_data hGc hGd hD hK hT hxs hfix hQ₂ hQ₃ hρ hTay
  have hmap := unstable_of_flipCoeff_neg_coord hP hPp hv hw hwv hS hC hρ₀ hTay' hk hab
  exact ⟨hmap, solution_unstable_of_map hGc hK hT hGper hxs hfix hmap⟩

/-- **Fields of class `C⁴`, stable side.** `orbit_stable_of_flipCoeff_pos` for a field with
`G(t, ·)` of class `C⁴`, `D_x²G`, `D_x³G` continuous along `x_*` and `‖D_x⁴G‖ ≤ B₄` on the tube
of radius `ρ` about `x_*`: the Taylor coefficients are `Q₂ = D_x²G/2 = taylor2 G x_*` and
`Q₃ = D_x³G/6 = taylor3 G x_*` (`PeriodMapTaylor.taylor_along_of_contDiff`). -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_flipCoeff_pos_of_contDiff
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) (taylor2 G xs) (taylor3 G xs) 0 T
          (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm k +
          secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T k vm))) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → Tendsto (fun t => x t - xs t) atTop (𝓝 0) :=
  orbit_stable_of_flipCoeff_pos hGc (fun t => (hG4 t).differentiable (by norm_num)) hD hK hT
    hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS hk hab

/-- **Fields of class `C⁴`, unstable side.** `orbit_unstable_of_flipCoeff_neg` with
`Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` along `x_*`, under the hypotheses of
`orbit_stable_of_flipCoeff_pos_of_contDiff`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_flipCoeff_neg_of_contDiff
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) • vm)
    (hab : (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) (taylor2 G xs) (taylor3 G xs) 0 T
          (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm k +
          secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T k vm)) < 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ :=
  orbit_unstable_of_flipCoeff_neg hGc (fun t => (hG4 t).differentiable (by norm_num)) hD hK hT
    hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS hk hab

end Orbit

end powerlib.Periodic.FlipOrbit
