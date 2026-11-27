import theorem.Periodic.FoldReduction
import theorem.Periodic.FlipOrbit

/-! # The fold reduction of a periodic solution, with the period map derived from the field

`theorem/Periodic/FoldReduction.lean` decides a fixed point with a simple multiplier `+1` and a
stable complement by the fold coefficient `a` and, at `a = 0`, by the cubic coefficient `b`, for a
map whose strict derivative and cubic Taylor expansion are hypotheses. Here the map is the period
map `P(ξ) = x(T; 0, ξ)` of a `T`-periodic, **non-autonomous** system `ẋ = G(t, x)` (a forced or
parametrically pumped system) at a `T`-periodic solution `x_*`, and these hypotheses are derived
from the field as in `theorem/Periodic/FlipOrbit.lean`: `P(x_*(0)) = x_*(0)`,
`DP(x_*(0)) = Φ(T, 0)` (`FlowDerivative.hasStrictFDerivAt_periodMap`) and
`P(p + e) = p + Φ(T, 0) e + P₂(e, e) + P₃(e, e, e) + O(‖e‖⁴)` with the second and third
variations (`PeriodMapTaylor.periodMap_taylor`). With `M vm = vm`, `wmᵀ M = wmᵀ`, `wm ⬝ vm = 1`
and `M − vm wmᵀ` Schur stable, the coefficients are `a = wm ⬝ P₂(vm, vm)` and
`b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))`,
`(I − M) k = P₂(vm, vm) − (wm ⬝ P₂(vm, vm)) vm`. The verdicts for the periodic solution: `a ≠ 0`
(fold or transcritical type) — the period map and `x_*` are unstable; `a = 0`, `b < 0` (pitchfork
type, supercritical side) — the period map is locally asymptotically, not exponentially, stable,
and `x_*` is Lyapunov stable and attracting; `a = 0`, `b > 0` — both are unstable. The step from
the period map to the solutions is `FlipOrbit.solution_stable_of_map` and
`FlipOrbit.solution_unstable_of_map`.

**Why autonomous systems are excluded.** For `ẋ = f(x)` the multiplier `+1` is the trivial
multiplier of every nonconstant periodic orbit, with the velocity `f(x_*(0))` as eigenvector
(`OrbitMultiplier`). There it is not a critical case of the kind decided here: every point
`x_*(s)` of the orbit is a fixed point of the period map (`periodMap_autonomous_orbit`), so the
fixed points accumulate at `x_*(0)`, the period map is never locally asymptotically stable there,
and both coefficients vanish identically, `a = b = 0`, whenever `+1` is simple with stable
complement (`autonomous_trivial_multiplier`, through
`FoldReduction.foldCoeffs_eq_zero_of_fixedPoints`): the reduction decides nothing. The question
for an autonomous orbit is orbital stability, through a Poincaré section transverse to the orbit,
which is not treated here.

Scope.
* As in `theorem/Periodic/FlipOrbit.lean`: solutions in `ℝ^{Fin n}` with the sup norm, the map
  semantics on `ℝⁿ = EuclideanSpace ℝ (Fin n)` through `FlipOrbit.euclidMap`; `G` is `T`-periodic
  in `t`, continuous, differentiable in `x` with `D_xG` jointly continuous, and globally
  `K`-Lipschitz in `x`; `x_*` is a global solution with `x_*(T) = x_*(0)`; along `x_*` on
  `[0, T]` the field has the cubic Taylor expansion with continuous coefficients and quartic
  remainder (for a field of class `C⁴` in `x`: the `_of_contDiff` theorems, with
  `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6`).
* The spectral hypothesis is the projector form of `FoldReduction.multipliers_of_deflateAt` at
  `μ = 1` for the monodromy matrix `M = monodromy (jacobianAlong G x_*) T 0`: `+1` simple, every
  other multiplier strictly inside the unit circle. `G` may be autonomous in the statements of the
  three verdicts; `autonomous_trivial_multiplier` shows that they are then vacuous for a
  nonconstant orbit (`a = b = 0`).
* The solution statements concern the initial time `0` (solutions on `[0, ∞)`); `a = b = 0` is
  not decided; orbital stability of autonomous orbits is not treated.
* Generic mathematics; no model family.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), Ch. 4 and Ch. 9 (the fold
and the cusp of fixed points of maps), §5.4 (the Poincaré map of a periodic orbit, its derivative
the monodromy matrix, its Taylor coefficients from the variational equations) and §1.5 (Poincaré
maps: the trivial multiplier `+1` of a cycle of an autonomous system, and the period map of a
periodically forced system); Hartman, *Ordinary Differential Equations*, Ch. V (the first
variation); the open items of
`theorem/Periodic/FlipOrbit.lean` (Scope: "Only the multiplier `−1` is reduced") and
`theorem/Periodic/CriticalMultiplier.lean` (Scope: "The multiplier `+1` of a nonconstant orbit is
not reduced").

Results.
* `coords_at` — the projector data of a simple multiplier `μ` and the cubic expansion of a map of
  `Fin n → ℝ`, read on `ℝⁿ` (the hypotheses of `FoldReduction`).
* `periodMap_data` — the strict derivative, the fixed point and the cubic expansion of the period
  map of a periodic solution, from the field.
* **The theorems**: `orbit_unstable_of_foldCoeff_ne_zero` (`a ≠ 0`: the period map and `x_*` are
  unstable), `orbit_stable_of_cubicCoeff_neg` (`a = 0`, `b < 0`: the period map is locally
  asymptotically, not exponentially, stable, and `x_*` is Lyapunov stable and attracting),
  `orbit_unstable_of_cubicCoeff_pos` (`a = 0`, `b > 0`: unstable); for fields of class `C⁴`:
  `orbit_unstable_of_foldCoeff_ne_zero_of_contDiff`, `orbit_stable_of_cubicCoeff_neg_of_contDiff`,
  `orbit_unstable_of_cubicCoeff_pos_of_contDiff`.
* Autonomous systems: `periodMap_autonomous_orbit` (every point of the orbit is a fixed point of
  the period map), `autonomous_trivial_multiplier` (the trivial multiplier `+1` with the velocity
  as eigenvector; the period map is not locally asymptotically stable; `a = b = 0` for every
  projector data of a simple `+1` with stable complement).

Corrections.
None: an extension (`FoldReduction` for the period map of a periodic system, with its regularity
derived from the field, and the exclusion of the trivial multiplier of autonomous orbits made
precise).

Family and connection conclusions.
None: static evidence on periodic ODEs (stability of a periodic solution at a multiplier `+1`).
-/

noncomputable section
namespace powerlib.Periodic.FoldOrbit

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor FlipOrbit FoldReduction

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The data of a simple multiplier `μ` read on `ℝⁿ` -/

/-- **The projector data at a multiplier `μ` in Euclidean coordinates.** For a map `F` of
`Fin n → ℝ` with fixed point `p`, strict derivative `Mm` there, the projector data
`Mm vm = μ vm`, `wmᵀ Mm = μ wmᵀ`, `wm ⬝ vm = 1` and a cubic Taylor expansion, all in the
coordinates `Fin n → ℝ` (sup norm): the hypotheses of `FoldReduction` for `euclidMap F` on `ℝⁿ`,
with the deflated matrix `Mm − μ vm wmᵀ`, every solution `k` of
`k − Mm k = P₂(vm, vm) − (wm ⬝ P₂(vm, vm)) vm` read as a solution of `(I − M) k = Q P₂(v, v)`,
and the coefficients `a`, `b(k)` unchanged. -/
@[tmio T, powerlib_foundation] theorem coords_at {F : (Fin n → ℝ) → Fin n → ℝ}
    {p : Fin n → ℝ} {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' Mm).toContinuousLinearMap p) (hFp : F p = p)
    {μ : ℝ} {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = μ • vm) (hw : wm ᵥ* Mm = μ • wm)
    (hwv : wm ⬝ᵥ vm = 1)
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖F (p + e) - p - Mm *ᵥ e - P₂ e e - P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4) :
    ∃ (vE : ℝⁿ) (wE : ℝⁿ →L[ℝ] ℝ) (P₂E : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ)
      (P₃E : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ℝⁿ) ℝⁿ) (ρ C' : ℝ),
      0 < ρ ∧
      HasStrictFDerivAt (euclidMap F) (Linear.op Mm) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) ∧
      euclidMap F ((EuclideanSpace.equiv (Fin n) ℝ).symm p) =
        (EuclideanSpace.equiv (Fin n) ℝ).symm p ∧
      Linear.op Mm vE = μ • vE ∧ (∀ e, wE (Linear.op Mm e) = μ * wE e) ∧ wE vE = 1 ∧
      Linear.op (Mm - μ • vecMulVec vm wm) = deflateAt (Linear.op Mm) vE wE μ ∧
      (∀ e, ‖e‖ ≤ ρ → ‖euclidMap F ((EuclideanSpace.equiv (Fin n) ℝ).symm p + e) -
        (EuclideanSpace.equiv (Fin n) ℝ).symm p - Linear.op Mm e - P₂E e e -
          P₃E (fun _ => e)‖ ≤ C' * ‖e‖ ^ 4) ∧
      wE (P₂E vE vE) = wm ⬝ᵥ P₂ vm vm ∧
      ∀ k : Fin n → ℝ, (k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm →
        (EuclideanSpace.equiv (Fin n) ℝ).symm k - Linear.op Mm
          ((EuclideanSpace.equiv (Fin n) ℝ).symm k) = FlipReduction.specProj vE wE (P₂E vE vE)) ∧
        wE (P₃E (fun _ => vE)) + wE (P₂E vE ((EuclideanSpace.equiv (Fin n) ℝ).symm k) +
          P₂E ((EuclideanSpace.equiv (Fin n) ℝ).symm k) vE) =
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
  refine ⟨ε.symm vm, wE, P₂E, P₃E, ρ₀ / (‖εL‖ + 1), ‖εS‖ * C * ‖εL‖ ^ 4,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k => ⟨fun hk => ?_, ?_⟩⟩
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
  · rw [hop, ContinuousLinearEquiv.apply_symm_apply, hv, map_smul]
  · intro e
    rw [hwEa, hwEa, hop, ContinuousLinearEquiv.apply_symm_apply, Matrix.dotProduct_mulVec, hw,
      smul_dotProduct, smul_eq_mul]
  · rw [hwEa, ContinuousLinearEquiv.apply_symm_apply, hwv]
  · ext1 y
    rw [deflateAt_apply, hop, hwEa]
    show ε.symm ((Mm - μ • vecMulVec vm wm) *ᵥ ε y) = _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, map_sub, op_smul_eq_smul,
      map_smul, map_smul, smul_smul]
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
  · rw [hwEa, hP₂Ea, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  · rw [hop, FlipReduction.specProj_apply, hwEa, hP₂Ea]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [← map_sub, hk, map_sub, map_smul]
  · rw [hwEa, hwEa, hP₃Ea, hP₂Ea, hP₂Ea, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, ← map_add, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]

/-! ## The period map of a periodic solution -/

section Orbit

variable {G : ℝ → (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

/-- **The data of the reduction, from the field.** For a `T`-periodic solution `x_*` of
`ẋ = G(t, x)` (`G` continuous, differentiable in `x` with `D_xG` jointly continuous, `K`-Lipschitz
in `x`) along which `G` has the cubic Taylor expansion with continuous coefficients
`D_xG(r, x_*(r))`, `Q₂(r)`, `Q₃(r)` and quartic remainder: the period map has at `x_*(0)` the
strict derivative `M = Φ(T, 0)` (`FlowDerivative.hasStrictFDerivAt_periodMap`), fixes `x_*(0)`,
and has the cubic expansion with the second and third variations `P₂(T)`, `P₃(T)` and a quartic
remainder (`PeriodMapTaylor.periodMap_taylor`, with the bounds of `Q₂`, `Q₃` on `[0, T]` from
their continuity). -/
@[tmio T, powerlib_foundation] theorem periodMap_data (hGc : Continuous (uncurry G))
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

/-- **The fold of a periodic solution: unstable.** Let `G` be `T`-periodic in `t`, continuous,
differentiable in `x` with `D_xG` jointly continuous, `K`-Lipschitz in `x`, and let `x_*` be a
solution with `x_*(T) = x_*(0)` along which `G` has the cubic Taylor expansion with continuous
coefficients `D_xG(r, x_*(r))`, `Q₂(r)`, `Q₃(r)` and quartic remainder. Let the monodromy
`M = Φ(T, 0) = monodromy (jacobianAlong G x_*) T 0` have a simple multiplier `+1` with stable
complement in projector form (`M vm = vm`, `wmᵀ M = wmᵀ`, `wm ⬝ vm = 1`, `M − vm wmᵀ` Schur
stable). If the fold coefficient `a = wm ⬝ P₂(vm, vm)` of the second variation `P₂ = P₂(T)` is not
zero, the period map (read on `ℝⁿ`) is unstable at `x_*(0)` and `x_*` is an unstable solution:
there is `ε > 0` such that solutions on `[0, ∞)` starting arbitrarily close to `x_*(0)` reach the
distance `ε` from `x_*`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_foldCoeff_ne_zero
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 - vecMulVec vm wm))
    (ha : wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm ≠ 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  obtain ⟨hP, hPp, C, ρ₀, hC, hρ₀, hTay'⟩ :=
    periodMap_data hGc hGd hD hK hT hxs hfix hQ₂ hQ₃ hρ hTay
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay'', ha', -⟩ :=
    coords_at (μ := 1) hP hPp (by rw [hv, one_smul]) (by rw [hw, one_smul]) hwv hC hρ₀ hTay'
  rw [one_smul] at hv' hL
  have hmap := unstable_of_foldCoeff_ne_zero_matrix hP' hPp' hv' (fun e => by rw [hw', one_mul])
    hwv' hL hS hρ' hTay'' (by rw [ha']; exact ha)
  exact ⟨hmap, solution_unstable_of_map hGc hK hT hGper hxs hfix hmap⟩

/-- **The pitchfork type of a periodic solution, stable side.** Under the hypotheses of
`orbit_unstable_of_foldCoeff_ne_zero`, let the fold coefficient vanish,
`a = wm ⬝ P₂(vm, vm) = 0`, and let `k − M k = P₂(vm, vm) − (wm ⬝ P₂(vm, vm)) vm`. If the cubic
coefficient `b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))` (`P₃ = P₃(T)` the third
variation; independent of the choice of `k`) is negative, then the period map (read on `ℝⁿ`) is
locally asymptotically, not exponentially, stable at `x_*(0)`, and `x_*` is a Lyapunov stable and
attracting solution: solutions on `[0, ∞)` that start close to `x_*(0)` stay close to `x_*`, and
those starting within some `δ` converge to it. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_cubicCoeff_neg
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 - vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (ha : wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm = 0)
    (hb : wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm) < 0) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → Tendsto (fun t => x t - xs t) atTop (𝓝 0) := by
  obtain ⟨hP, hPp, C, ρ₀, hC, hρ₀, hTay'⟩ :=
    periodMap_data hGc hGd hD hK hT hxs hfix hQ₂ hQ₃ hρ hTay
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay'', ha', hkb⟩ :=
    coords_at (μ := 1) hP hPp (by rw [hv, one_smul]) (by rw [hw, one_smul]) hwv hC hρ₀ hTay'
  rw [one_smul] at hv' hL
  obtain ⟨hk', hb'⟩ := hkb k
  have hmap := localAsymptoticStable_of_cubicCoeff_neg_matrix hP' hPp' hv'
    (fun e => by rw [hw', one_mul]) hwv' hL hS hρ' hTay'' (hk' hk) (by rw [ha']; exact ha)
    (by rw [hb']; exact hb)
  exact ⟨hmap, solution_stable_of_map hGc hK hT hGper hxs hfix hmap.1⟩

/-- **The pitchfork type of a periodic solution, unstable side.** Under the hypotheses of
`orbit_stable_of_cubicCoeff_neg` with a positive cubic coefficient `b`, the period map (read on
`ℝⁿ`) is unstable at `x_*(0)` and `x_*` is an unstable solution. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_cubicCoeff_pos
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 - vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (ha : wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm = 0)
    (hb : 0 < wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm)) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  obtain ⟨hP, hPp, C, ρ₀, hC, hρ₀, hTay'⟩ :=
    periodMap_data hGc hGd hD hK hT hxs hfix hQ₂ hQ₃ hρ hTay
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay'', ha', hkb⟩ :=
    coords_at (μ := 1) hP hPp (by rw [hv, one_smul]) (by rw [hw, one_smul]) hwv hC hρ₀ hTay'
  rw [one_smul] at hv' hL
  obtain ⟨hk', hb'⟩ := hkb k
  have hmap := unstable_of_cubicCoeff_pos_matrix hP' hPp' hv' (fun e => by rw [hw', one_mul])
    hwv' hL hS hρ' hTay'' (hk' hk) (by rw [ha']; exact ha) (by rw [hb']; exact hb)
  exact ⟨hmap, solution_unstable_of_map hGc hK hT hGper hxs hfix hmap⟩

/-- **Fields of class `C⁴`, fold type.** `orbit_unstable_of_foldCoeff_ne_zero` for a field with
`G(t, ·)` of class `C⁴`, `D_x²G`, `D_x³G` continuous along `x_*` and `‖D_x⁴G‖ ≤ B₄` on the tube of
radius `ρ` about `x_*`: the Taylor coefficients are `Q₂ = D_x²G/2 = taylor2 G x_*` and
`Q₃ = D_x³G/6 = taylor3 G x_*` (`PeriodMapTaylor.taylor_along_of_contDiff`). -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_foldCoeff_ne_zero_of_contDiff
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 - vecMulVec vm wm))
    (ha : wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm ≠ 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ :=
  orbit_unstable_of_foldCoeff_ne_zero hGc (fun t => (hG4 t).differentiable (by norm_num)) hD hK
    hT hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS ha

/-- **Fields of class `C⁴`, pitchfork type, stable side.** `orbit_stable_of_cubicCoeff_neg` with
`Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` along `x_*`, under the hypotheses of
`orbit_unstable_of_foldCoeff_ne_zero_of_contDiff`. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_cubicCoeff_neg_of_contDiff
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 - vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) • vm)
    (ha : wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm = 0)
    (hb : wm ⬝ᵥ thirdVariation (jacobianAlong G xs) (taylor2 G xs) (taylor3 G xs) 0 T
          (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm k +
          secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T k vm) < 0) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) →
      ‖x 0 - xs 0‖ < δ → Tendsto (fun t => x t - xs t) atTop (𝓝 0) :=
  orbit_stable_of_cubicCoeff_neg hGc (fun t => (hG4 t).differentiable (by norm_num)) hD hK hT
    hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS hk ha hb

/-- **Fields of class `C⁴`, pitchfork type, unstable side.** `orbit_unstable_of_cubicCoeff_pos`
with `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` along `x_*`, under the hypotheses of
`orbit_unstable_of_foldCoeff_ne_zero_of_contDiff`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_cubicCoeff_pos_of_contDiff
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 - vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) • vm)
    (ha : wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm = 0)
    (hb : 0 < wm ⬝ᵥ thirdVariation (jacobianAlong G xs) (taylor2 G xs) (taylor3 G xs) 0 T
          (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm k +
          secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T k vm)) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xs t‖ :=
  orbit_unstable_of_cubicCoeff_pos hGc (fun t => (hG4 t).differentiable (by norm_num)) hD hK hT
    hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS hk ha hb

end Orbit

/-! ## Autonomous systems: why the trivial multiplier `+1` is excluded -/

section Autonomous

variable {f : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

/-- **Along an autonomous periodic orbit every point is fixed by the period map.** For `ẋ = f(x)`
(`f` `K`-Lipschitz) and a `T`-periodic solution `x_*`, `P(x_*(s)) = x_*(s + T) = x_*(s)` for
every `s`: the time-shifted orbit is a solution from `x_*(s)`. -/
@[tmio T, powerlib_foundation] theorem periodMap_autonomous_orbit (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 ≤ T)
    (hper : Periodic xs T) (s : ℝ) :
    periodMap (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) T (xs s) =
      xs s := by
  have hy : ∀ t, HasDerivAt (fun t => xs (t + s)) (f (xs (t + s))) t := fun t =>
    HasDerivAt.comp_add_const t s (hxs (t + s))
  have h := periodMap_fixed (G := fun _ => f) (hfK.continuous.comp continuous_snd)
    (fun _ => hfK) (xs := fun t => xs (t + s)) hy hT (by simp [add_comm T s, hper s])
  simpa using h

/-- The fourth derivative of a `C⁴` field is bounded on the tube of radius `1` about a periodic
orbit (a compact set). -/
@[tmio T, powerlib_foundation] private theorem exists_bound_tube (hf : ContDiff ℝ 4 f)
    {xs : ℝ → Fin n → ℝ} (hxc : Continuous xs) (T : ℝ) :
    ∃ B₄, ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) 1, ‖iteratedFDeriv ℝ 4 f y‖ ≤ B₄ := by
  set S := (fun q : ℝ × (Fin n → ℝ) => xs q.1 + q.2) '' (Icc 0 T ×ˢ Metric.closedBall 0 1)
    with hS
  have hSc : IsCompact S := (isCompact_Icc.prod (isCompact_closedBall 0 1)).image
    ((hxc.comp continuous_fst).add continuous_snd)
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv le_rfl).continuousOn
  refine ⟨B, fun r hr y hy => ?_⟩
  have hyS : y ∈ S := ⟨(r, y - xs r), ⟨hr, by
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]; exact hy⟩, by simp⟩
  simpa using hB y hyS

/-- **The trivial multiplier of an autonomous periodic orbit decides nothing.** For `ẋ = f(x)`
with `f` of class `C⁴` and `K`-Lipschitz, and a nonconstant `T`-periodic solution `x_*`
(`f(x_*(0)) ≠ 0`): the velocity `f(x_*(0))` is an eigenvector of the monodromy `M` with
multiplier `1` (`monodromy_mulVec_velocity`, `one_mem_spectrum_monodromy`); the period map is not
locally asymptotically stable at `x_*(0)`, since the orbit consists of fixed points accumulating
at `x_*(0)`; and for every projector data of a simple multiplier `+1` with stable complement
(`M vm = vm`, `wmᵀ M = wmᵀ`, `wm ⬝ vm = 1`, `M − vm wmᵀ` Schur stable — an orbitally hyperbolic
orbit) the fold coefficient `a = wm ⬝ P₂(vm, vm)` and the cubic coefficient `b` vanish
(`FoldReduction.foldCoeffs_eq_zero_of_fixedPoints`). So for autonomous systems the reduction at
`+1` never applies; their periodic orbits call for orbital stability (a Poincaré section), not for
the fold and pitchfork verdicts of a non-autonomous periodic solution. -/
@[tmio T, powerlib_foundation] theorem autonomous_trivial_multiplier (hf : ContDiff ℝ 4 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) :
    monodromy (variationalMatrix f xs) T 0 *ᵥ f (xs 0) = f (xs 0) ∧
    (1 : ℂ) ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)) ∧
    ¬ Map.LocalAsymptoticStable
        (euclidMap (periodMap (G := fun _ => f) (hfK.continuous.comp continuous_snd)
          (fun _ => hfK) T)) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∀ vm wm : Fin n → ℝ, monodromy (variationalMatrix f xs) T 0 *ᵥ vm = vm →
      wm ᵥ* monodromy (variationalMatrix f xs) T 0 = wm → wm ⬝ᵥ vm = 1 →
      LTI.SchurStable (monodromy (variationalMatrix f xs) T 0 - vecMulVec vm wm) →
      wm ⬝ᵥ secondVariation (variationalMatrix f xs) (taylor2 (fun _ => f) xs) 0 T vm vm = 0 ∧
      ∀ k : Fin n → ℝ, k - monodromy (variationalMatrix f xs) T 0 *ᵥ k =
          secondVariation (variationalMatrix f xs) (taylor2 (fun _ => f) xs) 0 T vm vm -
            (wm ⬝ᵥ secondVariation (variationalMatrix f xs) (taylor2 (fun _ => f) xs) 0 T
              vm vm) • vm →
        wm ⬝ᵥ thirdVariation (variationalMatrix f xs) (taylor2 (fun _ => f) xs)
            (taylor3 (fun _ => f) xs) 0 T (fun _ => vm) +
          wm ⬝ᵥ (secondVariation (variationalMatrix f xs) (taylor2 (fun _ => f) xs) 0 T vm k +
            secondVariation (variationalMatrix f xs) (taylor2 (fun _ => f) xs) 0 T k vm) = 0 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  set hGc : Continuous (uncurry fun (_ : ℝ) => f) := hfK.continuous.comp continuous_snd
  set P := periodMap (G := fun _ => f) hGc (fun _ => hfK) T with hPdef
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (E.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  -- the orbit is a curve of fixed points accumulating at `x_*(0)`
  have hacc0 : ∀ η > 0, ∃ s, xs s ≠ xs 0 ∧ ‖xs s - xs 0‖ < η := by
    intro η hη
    by_contra hcon
    push Not at hcon
    have hev : xs =ᶠ[𝓝 0] fun _ => xs 0 := by
      filter_upwards [hxc.continuousAt.eventually (Metric.ball_mem_nhds (xs 0) hη)] with s hs
      by_contra hne'
      rw [dist_eq_norm] at hs
      exact absurd (hcon s hne') (not_le.mpr hs)
    have h0 : HasDerivAt xs 0 0 := (hasDerivAt_const 0 (xs 0)).congr_of_eventuallyEq hev
    exact hne ((hxs 0).unique h0)
  have hacc : ∀ δ > 0, ∃ q, euclidMap P q = q ∧ q ≠ E.symm (xs 0) ∧ ‖q - E.symm (xs 0)‖ < δ := by
    intro δ hδ
    obtain ⟨s, hs0, hsd⟩ := hacc0 (δ / (‖εS‖ + 1)) (by positivity)
    refine ⟨E.symm (xs s), ?_, fun h => hs0 (E.symm.injective h), ?_⟩
    · show E.symm (P (E (E.symm (xs s)))) = E.symm (xs s)
      rw [ContinuousLinearEquiv.apply_symm_apply, hPdef,
        periodMap_autonomous_orbit hfK hxs hT.le hper s]
    · rw [← map_sub]
      calc ‖E.symm (xs s - xs 0)‖ ≤ ‖εS‖ * ‖xs s - xs 0‖ := εS.le_opNorm _
        _ ≤ (‖εS‖ + 1) * ‖xs s - xs 0‖ := by gcongr; linarith
        _ < (‖εS‖ + 1) * (δ / (‖εS‖ + 1)) := by gcongr
        _ = δ := by field_simp
  refine ⟨monodromy_mulVec_velocity hf1 hxs hT hper,
    one_mem_spectrum_monodromy hf1 hxs hT hper hne,
    not_localAsymptoticStable_of_fixedPoints hacc, fun vm wm hv hw hwv hS => ?_⟩
  -- the data of the period map, from the field
  have hfix : xs T = xs 0 := by simpa using hper 0
  have hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ f) (xs r) :=
    ((hf.fderiv_right (m := 3) (by norm_num)).continuous_fderiv (by norm_num)).comp hxc
  have hD3 : Continuous fun r => iteratedFDeriv ℝ 3 f (xs r) :=
    (hf.continuous_iteratedFDeriv (by norm_num)).comp hxc
  obtain ⟨B₄, hB4⟩ := exists_bound_tube hf hxc T
  obtain ⟨hP, hPp, C, ρ₀, hC, hρ₀, hTay⟩ := periodMap_data (G := fun _ => f) hGc
    (fun _ => hf.differentiable (by norm_num))
    ((hf.continuous_fderiv (by norm_num)).comp continuous_snd) (fun _ => hfK) hT hxs hfix
    (Q₂ := taylor2 (fun _ => f) xs) (Q₃ := taylor3 (fun _ => f) xs)
    (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) one_pos
    (taylor_along_of_contDiff (fun r _ y _ => hf.contDiffAt) hB4)
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay', ha', hkb⟩ :=
    coords_at (μ := 1) hP hPp (by rw [jacobianAlong_const, hv, one_smul])
      (by rw [jacobianAlong_const, hw, one_smul]) hwv hC hρ₀ hTay
  rw [one_smul] at hv' hL
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [← jacobianAlong_const, hL] at hLm
  obtain ⟨ha, hb, -⟩ := foldCoeffs_eq_zero_of_fixedPoints hP' hPp' hv'
    (fun e => by rw [hw', one_mul]) hwv' hm hLm hρ' hTay' hacc
  refine ⟨ha'.symm.trans ha, fun k hk => ?_⟩
  obtain ⟨hk', hb'⟩ := hkb k
  exact hb'.symm.trans (hb _ (hk' hk))

end Autonomous

end powerlib.Periodic.FoldOrbit
