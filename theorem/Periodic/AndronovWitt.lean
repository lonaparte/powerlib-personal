import theorem.Periodic.PoincareSection
import theorem.Periodic.FlipOrbitUniform
import theorem.Periodic.OrbitalInstability
import theorem.Periodic.LocalField

/-! # The Andronov–Witt theorem: orbital stability and instability of autonomous periodic orbits

A nonconstant `T`-periodic orbit `x_*` of an autonomous system `ẋ = f(x)` always has the trivial
multiplier `1` (velocity direction), so its period map is never asymptotically stable
(`FoldOrbit.autonomous_trivial_multiplier`) and the periodic solution itself is at best Lyapunov
stable: nearby solutions drift in phase. The correct notion is **orbital** stability, decided by
the **nontrivial** multipliers through the Poincaré map `Π` of a section transverse to the orbit
(`theorem/Periodic/PoincareSection.lean`), whose Jacobian `DΠ(p) = sectionMatrix M f(p)` has those
multipliers as its eigenvalues on the section.

* **Stable side (Andronov–Witt).** If `DΠ(p)` is Schur stable — equivalently `M − f(p) wᵀ` is
  Schur stable for some `w ⬝ f(p) = 1`, equivalently `1` is a simple multiplier and all other
  multipliers lie strictly inside the unit circle (`PoincareSection.schurStable_deflate_iff`) —
  then `Π` is locally exponentially stable (`Map.locallyExponentiallyStable_of_schurStable`), and
  this gives the orbit **asymptotic phase**: every solution starting within `δ` of `x_*(σ)` has a
  phase `θ`, `|θ| ≤ C ‖x(0) − x_*(σ)‖`, with
  `‖x(t) − x_*(t + σ + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(σ)‖`, and the distance to the orbit decays,
  `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))`. The proof samples the solution at its
  successive crossings `t_k = τ₀ + ⋯ + τ_{k−1}` of the section (`iterate_poincareMap`): the
  crossing points converge geometrically to `p`, the return times `τ_k` converge geometrically to
  `T` (the return time is Lipschitz at `p`), so `t_k − kT` converges to `−θ` with a geometric tail,
  and Grönwall on `[t_k, t_{k+1}]` interpolates between the crossings.
* **Unstable side.** If a multiplier has `|μ| > 1` (necessarily nontrivial), it is an eigenvalue of
  `DΠ(p)` (`PoincareSection.mem_spectrum_deflate_iff`) and `Π` is unstable
  (`Map.unstable_of_eigenvalue`). The escaping orbit of `Π` leaves a small ball about `p` through
  a point of the section, and near `p` the section meets the orbit only in `p`
  (`orbit_section_eq`); a compactness argument turns the escape into a positive distance from
  the whole orbit: the orbit is **orbitally unstable** (`orbit_unstable`).

Scope.
* `ẋ = f(x)` on `ℝ^{Fin n}` with the sup norm, continuous time, solutions on `[0, ∞)` (Mathlib
  `IsIntegralCurveOn`); `f` of class `C¹` and globally `K`-Lipschitz (as in
  `theorem/Periodic/PoincareSection.lean`). The `_local` theorems drop the Lipschitz bound: `f` is
  replaced by the cut-off field `f ∘ ψ_R` of `theorem/Periodic/LocalField.lean`, equal to `f`
  within distance `1` of the orbit, and the verdicts are transferred back (on the stable side the
  solutions starting near the orbit exist on `[0, ∞)` and are unique; on the unstable side the
  escaping solutions are solutions of `f` on segments `[0, t]`). `x_*` is a global `T`-periodic
  solution, `T > 0`, `f(x_*(0)) ≠ 0`; `T` need not be the minimal period.
* The map semantics on `ℝⁿ = EuclideanSpace ℝ (Fin n)` is used through `FlipOrbit.euclidMap`
  (`poincareMap_stability`); the solution statements are in the sup norm. Orbital distance is
  `Metric.infDist` to the range of `x_*`.
* The constants `δ`, `C`, `λ` are not explicit here: the rate is `λ = −log q/(3T/2)` with
  `q < 1` a geometric rate of `Π` (from the Schur stability of `DΠ(p)`). Every rate
  `λ < −log ρ(DΠ(p))/T`, with a Lipschitz asymptotic phase, and the optimality of `−log ρ/T` are
  `theorem/Periodic/AndronovWittRate.lean`; explicit closed-form constants, for `Df` globally
  Lipschitz and a contraction datum `‖(M − f(p) wᵀ)^N‖ ≤ q < 1` (equivalent to the Schur
  stability of the deflation), are `theorem/Periodic/AndronovWittQuantitative.lean`. In the
  critical case (a nontrivial multiplier on the unit circle, the others inside) the multipliers
  decide nothing; the transfer of the verdict of `Π` to the orbit and its flip/fold reductions are
  `theorem/Periodic/AndronovWittCritical.lean`, planar counterexamples
  `theorem/Periodic/CriticalCycles.lean`.
* Generic mathematics; no model family.

Source: A. A. Andronov and A. A. Witt, "Zur Stabilität nach Liapounoff", Phys. Z. Sowjetunion 4
(1933) (orbital stability of a cycle from its nontrivial multipliers); Coddington and Levinson,
*Theory of Ordinary Differential Equations*, Ch. 13 §2 (orbital asymptotic stability with
asymptotic phase); Hartman, *Ordinary Differential Equations* (the asymptotic phase);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §1.5 (the Poincaré map of a cycle
and its multipliers); Hirsch, Smale and Devaney, *Differential Equations, Dynamical Systems, and
an Introduction to Chaos*, Ch. 10; the open item of `theorem/Periodic/FoldOrbit.lean` (Scope:
"orbital asymptotic stability of autonomous orbits is not treated";
`autonomous_trivial_multiplier`: "the remaining question, orbital asymptotic stability, needs a
Poincaré section transverse to the orbit").

Results.
* `iterate_poincareMap` — `Πᵏ(x(0)) = x(τ₀ + ⋯ + τ_{k−1})` for every solution `x` on `[0, ∞)`.
* **Stable side**: `asymptoticPhase_of_section` (from `x_*(0)`), `asymptoticPhase` (uniformly
  from every point `x_*(σ)`: asymptotic phase with exponential rate), `infDist_orbit_le`
  (orbital exponential stability: `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))`).
* **Unstable side**: `orbit_section_eq` (near `x_*(0)` the section meets the orbit only in
  `x_*(0)`), `orbit_unstable` (a multiplier `|μ| > 1` makes the orbit orbitally unstable).
* `poincareMap_stability` — the Poincaré map in the map semantics: locally exponentially stable
  for a Schur stable `DΠ(p)`, unstable for a multiplier `|μ| > 1`.
* **The theorem** `andronov_witt` (deflated form: `M − f(p) wᵀ` Schur stable for some
  `w ⬝ f(p) = 1`) and `andronov_witt_of_multipliers` (`1` simple, all other multipliers strictly
  inside the unit circle): asymptotic phase and orbital exponential stability.
* Without a global Lipschitz bound: `andronov_witt_local` (existence near the orbit, asymptotic
  phase, orbital exponential stability) and `orbit_unstable_local` (orbital instability through
  solutions on segments).

Corrections.
None: an extension (orbital asymptotic stability with asymptotic phase and orbital instability of
autonomous periodic orbits, which `theorem/Periodic/FoldOrbit.lean` left open).

Family and connection conclusions.
None: static evidence on autonomous ODEs (orbital stability of a periodic orbit).
-/

noncomputable section
namespace powerlib.Periodic.AndronovWitt

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative FlipOrbit PoincareSection

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Iterates of the Poincaré map are the solution at the accumulated return times -/

/-- **The orbit of the Poincaré map is the solution sampled at the return times.** If the return
times of the first `k` iterates are nonnegative, `Πᵏ(x(0)) = x(t_k)` with
`t_k = τ(x(0)) + τ(Π(x(0))) + ⋯ + τ(Π^{k−1}(x(0)))`, for every solution `x` on `[0, ∞)`. -/
@[tmio T, powerlib_foundation] theorem iterate_poincareMap (hfK : LipschitzWith K f)
    (τ : (Fin n → ℝ) → ℝ) {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (k : ℕ) (hτ : ∀ j < k, 0 ≤ τ ((poincareMap hfK τ)^[j] (x 0))) :
    (poincareMap hfK τ)^[k] (x 0) =
      x (∑ j ∈ Finset.range k, τ ((poincareMap hfK τ)^[j] (x 0))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => hτ j (Nat.lt_succ_of_lt hj))
    set tk := ∑ j ∈ Finset.range k, τ ((poincareMap hfK τ)^[j] (x 0)) with htk
    have htk0 : 0 ≤ tk :=
      Finset.sum_nonneg fun j hj => hτ j (Nat.lt_succ_of_lt (Finset.mem_range.1 hj))
    have hy : IsIntegralCurveOn (fun r => x (r + tk)) (fun _ => f) (Ici 0) :=
      (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
        (Ici_subset_Ici.2 (by linarith))
    have hy0 : x (0 + tk) = (poincareMap hfK τ)^[k] (x 0) := by
      rw [zero_add]; exact ih'.symm
    have hτk := hτ k (Nat.lt_succ_self k)
    have h := poincareMap_eq hfK τ hy (by rw [hy0]; exact hτk)
    rw [hy0] at h
    rw [Function.iterate_succ_apply', Finset.sum_range_succ, h, add_comm]

/-! ## Maps of `Fin n → ℝ` read in the map semantics -/

/-- A strict derivative and a fixed point of a map of `Fin n → ℝ`, read for `euclidMap` on
`ℝⁿ`. -/
@[tmio T, powerlib_foundation] private theorem euclid_data {F : (Fin n → ℝ) → Fin n → ℝ}
    {p : Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' A).toContinuousLinearMap p) (hFp : F p = p) :
    HasStrictFDerivAt (euclidMap F) (Linear.op A) ((EuclideanSpace.equiv (Fin n) ℝ).symm p) ∧
      euclidMap F ((EuclideanSpace.equiv (Fin n) ℝ).symm p) =
        (EuclideanSpace.equiv (Fin n) ℝ).symm p := by
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  have h1 : HasStrictFDerivAt F (Matrix.toLin' A).toContinuousLinearMap (ε (ε.symm p)) := by
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have h := (ε.symm.hasStrictFDerivAt (x := F (ε (ε.symm p)))).comp (ε.symm p)
    (h1.comp (ε.symm p) ε.hasStrictFDerivAt)
  have hfun : euclidMap F = fun x => ε.symm (F (ε x)) := rfl
  have hM : Linear.op A = (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ).comp
      ((Matrix.toLin' A).toContinuousLinearMap.comp (ε : ℝⁿ →L[ℝ] (Fin n → ℝ))) := by
    ext1 y; rfl
  refine ⟨by rw [hfun, hM]; exact h, ?_⟩
  show ε.symm (F (ε (ε.symm p))) = ε.symm p
  rw [ContinuousLinearEquiv.apply_symm_apply, hFp]

/-! ## Local exponential stability of a map, in the sup norm -/

/-- A map of `Fin n → ℝ` with fixed point `p` and Schur stable strict derivative `A` there is
locally exponentially stable in the sup norm (`Map.locallyExponentiallyStable_of_schurStable`,
read through `euclidMap`), with a rate `0 < q < 1`. -/
@[tmio T, powerlib_foundation] private theorem exp_stable_coord {F : (Fin n → ℝ) → Fin n → ℝ}
    {p : Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' A).toContinuousLinearMap p) (hFp : F p = p)
    (hA : LTI.SchurStable A) :
    ∃ r C q : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < q ∧ q < 1 ∧
      ∀ ξ, ‖ξ - p‖ < r → ∀ k : ℕ, ‖F^[k] ξ - p‖ ≤ C * q ^ k * ‖ξ - p‖ := by
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (ε : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  obtain ⟨hE, hEp⟩ := euclid_data hF hFp
  obtain ⟨r, C, q, hr, hC, hq0, hq1, hb⟩ :=
    Map.locallyExponentiallyStable_of_schurStable hE.hasFDerivAt hEp hA
  set q' := max q (1 / 2) with hq'
  have hq'0 : 0 < q' := lt_max_of_lt_right (by norm_num)
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  refine ⟨r / (‖εS‖ + 1), ‖εL‖ * C * ‖εS‖ + 1, q', by positivity,
    le_add_of_nonneg_left (by positivity), hq'0, hq'1, fun ξ hξ k => ?_⟩
  have hξE : ‖ε.symm ξ - ε.symm p‖ < r := by
    rw [← map_sub]
    calc ‖ε.symm (ξ - p)‖ ≤ ‖εS‖ * ‖ξ - p‖ := εS.le_opNorm _
      _ ≤ (‖εS‖ + 1) * ‖ξ - p‖ := by nlinarith [norm_nonneg (ξ - p)]
      _ < r := by rwa [lt_div_iff₀' (by positivity)] at hξ
  have hk := hb (ε.symm ξ) hξE k
  rw [iterate_euclidMap, ContinuousLinearEquiv.apply_symm_apply, ← map_sub] at hk
  rw [← map_sub] at hk
  have hqk : q ^ k ≤ q' ^ k := pow_le_pow_left₀ hq0 (le_max_left _ _) k
  calc ‖F^[k] ξ - p‖ = ‖ε (ε.symm (F^[k] ξ - p))‖ := by
        rw [ContinuousLinearEquiv.apply_symm_apply]
    _ ≤ ‖εL‖ * ‖ε.symm (F^[k] ξ - p)‖ := εL.le_opNorm _
    _ ≤ ‖εL‖ * (C * q ^ k * ‖ε.symm (ξ - p)‖) := by gcongr
    _ ≤ ‖εL‖ * (C * q' ^ k * (‖εS‖ * ‖ξ - p‖)) := by
        have hC0 : (0 : ℝ) ≤ C := by linarith
        have h2 : C * q ^ k ≤ C * q' ^ k := mul_le_mul_of_nonneg_left hqk hC0
        have h3 : ‖ε.symm (ξ - p)‖ ≤ ‖εS‖ * ‖ξ - p‖ := εS.le_opNorm _
        have h4 : C * q ^ k * ‖ε.symm (ξ - p)‖ ≤ C * q' ^ k * (‖εS‖ * ‖ξ - p‖) :=
          mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ ≤ (‖εL‖ * C * ‖εS‖ + 1) * q' ^ k * ‖ξ - p‖ := by
        have := pow_nonneg hq'0.le k
        have := norm_nonneg (ξ - p)
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg εL) (by linarith : (0 : ℝ) ≤ C))
          (norm_nonneg εS)]

/-! ## Orbital asymptotic stability with asymptotic phase -/

/-- The orbit of a `T`-periodic solution of `ẋ = f(x)` moves with bounded speed:
`‖x_*(a) − x_*(b)‖ ≤ B |a − b|`. -/
@[tmio T, powerlib_foundation] private theorem exists_speed_bound (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b, ‖xs a - xs b‖ ≤ B * |a - b| := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (hfK.continuous.comp hxc).continuousOn
  have hBall : ∀ t, ‖f (xs t)‖ ≤ B := fun t => by
    obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hT t
    rw [hty]
    exact hB y (Ico_subset_Icc_self hy)
  refine ⟨max B 0, le_max_right _ _, fun a b => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
    (fun t _ => (hxs t).hasDerivWithinAt) (fun t _ => (hBall t).trans (le_max_left B 0))
    convex_univ (mem_univ b) (mem_univ a)
  rwa [Real.norm_eq_abs] at h

/-- **Andronov–Witt at the point `x_*(0)`, with asymptotic phase.** Let `x_*` be a nonconstant
`T`-periodic orbit of `ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz) whose Poincaré Jacobian
`sectionMatrix M f(x_*(0))` is Schur stable. Then there are `δ > 0`, `C ≥ 0` and a rate `λ > 0`
such that every solution `x` on `[0, ∞)` with `‖x(0) − x_*(0)‖ < δ` has an asymptotic phase `θ`,
`|θ| ≤ C ‖x(0) − x_*(0)‖`, with
`‖x(t) − x_*(t + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(0)‖` for all `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_of_section (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (hS : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)))) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs 0‖ < δ →
      ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs 0‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs 0‖ := by
  obtain ⟨τ, hτp, hτD, ⟨r, s, hr, hs, hsT, hsec, -⟩, hPp, hPD, -, -, -, -⟩ :=
    exists_poincareMap hf hfK hxs hT hper hne
  set P := poincareMap hfK τ with hP
  set p := xs 0 with hp
  obtain ⟨r₁, C₁, q, hr₁, hC₁, hq0, hq1, hexp⟩ := exp_stable_coord hPD hPp hS
  -- the return time is Lipschitz at `p`
  obtain ⟨L₀, hL₀⟩ := hτD.hasFDerivAt.isBigO_sub.bound
  obtain ⟨r₂, hr₂, hτL₀⟩ := Metric.eventually_nhds_iff.1 hL₀
  set L := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hτL : ∀ ξ, ‖ξ - p‖ < r₂ → |τ ξ - T| ≤ L * ‖ξ - p‖ := fun ξ hξ => by
    have h := hτL₀ (show dist ξ p < r₂ by rwa [dist_eq_norm])
    rw [Real.norm_eq_abs, hτp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨B, hB0, hB⟩ := exists_speed_bound hfK hxs hT hper
  -- the constants
  set c₀ := 3 * T / 2 with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set lam := -Real.log q / c₀ with hlam
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hlam0 : 0 < lam := div_pos (by linarith) hc₀0
  have h1q : 0 < 1 - q := by linarith
  set Cθ := L * C₁ / (1 - q) with hCθ
  set Cx := Real.exp (K * c₀) * (C₁ + B * Cθ) / q with hCx
  have hCθ0 : 0 ≤ Cθ := by positivity
  have hCx0 : 0 ≤ Cx := by positivity
  set δ := min r₁ (min r r₂ / C₁) with hδ
  have hC₁0 : 0 < C₁ := by linarith
  have hδ0 : 0 < δ := lt_min hr₁ (div_pos (lt_min hr hr₂) hC₁0)
  refine ⟨δ, max Cθ Cx, lam, hδ0, le_max_of_le_left hCθ0, hlam0, fun x hx hx0 => ?_⟩
  set ξ := x 0 with hξ
  set d := ‖ξ - p‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  -- the iterates stay in the box of the section
  have hy : ∀ k : ℕ, ‖P^[k] ξ - p‖ ≤ C₁ * q ^ k * d := hexp ξ (hx0.trans_le (min_le_left _ _))
  have hy' : ∀ k : ℕ, ‖P^[k] ξ - p‖ < min r r₂ := fun k => by
    have h1 : C₁ * q ^ k * d ≤ C₁ * d := by
      have := pow_le_one₀ hq0.le hq1.le (n := k)
      have : C₁ * q ^ k ≤ C₁ * 1 := mul_le_mul_of_nonneg_left this hC₁0.le
      nlinarith
    have h2 : C₁ * d < min r r₂ := by
      have := hx0.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀' hC₁0] at this
    exact (hy k).trans_lt (h1.trans_lt h2)
  have hτs : ∀ k : ℕ, |τ (P^[k] ξ) - T| < s := fun k =>
    (hsec _ ((hy' k).trans_le (min_le_left _ _))).1
  have hτpos : ∀ k : ℕ, T / 2 ≤ τ (P^[k] ξ) := fun k => by
    have := abs_lt.1 (hτs k); linarith
  have hτup : ∀ k : ℕ, τ (P^[k] ξ) ≤ c₀ := fun k => by
    have := abs_lt.1 (hτs k); rw [hc₀]; linarith
  have hτT : ∀ k : ℕ, |τ (P^[k] ξ) - T| ≤ L * C₁ * d * q ^ k := fun k => by
    refine (hτL _ ((hy' k).trans_le (min_le_right _ _))).trans ?_
    calc L * ‖P^[k] ξ - p‖ ≤ L * (C₁ * q ^ k * d) := mul_le_mul_of_nonneg_left (hy k) hL0
      _ = L * C₁ * d * q ^ k := by ring
  -- the accumulated return times
  set tt : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, τ (P^[j] ξ) with htt
  have htt_iter : ∀ k : ℕ, P^[k] ξ = x (tt k) := fun k =>
    iterate_poincareMap hfK τ hx k fun j _ => le_trans (by linarith) (hτpos j)
  have htt_succ : ∀ k : ℕ, tt (k + 1) = tt k + τ (P^[k] ξ) := fun k =>
    Finset.sum_range_succ _ _
  have htt_ge : ∀ k : ℕ, (k : ℝ) * (T / 2) ≤ tt k := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτpos k]
  have htt_le : ∀ k : ℕ, tt k ≤ k * c₀ := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτup k]
  -- the phase
  set u : ℕ → ℝ := fun j => τ (P^[j] ξ) - T with hu
  have hgeom : HasSum (fun j : ℕ => L * C₁ * d * q ^ j) (L * C₁ * d * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have husum : Summable u :=
    Summable.of_norm_bounded hgeom.summable fun j => by rw [Real.norm_eq_abs]; exact hτT j
  set θ' := ∑' j, u j with hθ'
  have htail : ∀ k : ℕ, |tt k - k * T - θ'| ≤ Cθ * d * q ^ k := fun k => by
    have hsplit := husum.sum_add_tsum_nat_add k
    have hsum : tt k - k * T = ∑ j ∈ Finset.range k, u j := by
      simp only [htt, hu, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have he : tt k - k * T - θ' = -∑' j, u (j + k) := by
      rw [hsum, hθ', ← hsplit]; ring
    rw [he, abs_neg]
    have hg : HasSum (fun j : ℕ => L * C₁ * d * q ^ k * q ^ j)
        (L * C₁ * d * q ^ k * (1 - q)⁻¹) :=
      (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
    have hb := tsum_of_norm_bounded hg fun j => by
      rw [Real.norm_eq_abs]
      calc |u (j + k)| ≤ L * C₁ * d * q ^ (j + k) := hτT (j + k)
        _ = L * C₁ * d * q ^ k * q ^ j := by rw [pow_add]; ring
    rw [Real.norm_eq_abs] at hb
    calc |∑' j, u (j + k)| ≤ L * C₁ * d * q ^ k * (1 - q)⁻¹ := hb
      _ = Cθ * d * q ^ k := by rw [hCθ]; field_simp
  refine ⟨-θ', ?_, fun t ht => ?_⟩
  · have h := htail 0
    simp only [htt, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
      zero_sub, abs_neg, pow_zero, mul_one] at h
    rw [abs_neg]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0)
  -- the period containing `t`
  have hex : ∃ k : ℕ, t < tt (k + 1) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (t / (T / 2))
    refine ⟨k, lt_of_lt_of_le ?_ (htt_ge (k + 1))⟩
    rw [div_lt_iff₀ (by positivity)] at hk
    push_cast; nlinarith
  classical
  set k := Nat.find hex with hk
  have hk1 : t < tt (k + 1) := Nat.find_spec hex
  have hk0 : tt k ≤ t := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simpa [htt] using ht
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact not_lt.1 this
  -- Grönwall on `[t_k, t]`
  have hxs' : IsIntegralCurveOn (fun r => xs (r + -θ')) (fun _ => f) (Icc (tt k) t) :=
    fun r _ => ((hxs (r + -θ')).comp_add_const r (-θ')).hasDerivWithinAt
  have htk0 : 0 ≤ tt k := le_trans (by positivity) (htt_ge k)
  have hxI : IsIntegralCurveOn x (fun _ => f) (Icc (tt k) t) :=
    hx.mono fun q hq => mem_Ici.2 (htk0.trans hq.1)
  have hgr := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK) hxI hxs' t ⟨hk0, le_rfl⟩
  rw [dist_eq_norm, dist_eq_norm] at hgr
  -- the deviation at the crossing `t_k`
  have hdev : ‖x (tt k) - xs (tt k + -θ')‖ ≤ (C₁ + B * Cθ) * q ^ k * d := by
    have hpk : xs (k * T) = p := hper.nat_mul_eq k
    calc ‖x (tt k) - xs (tt k + -θ')‖ = ‖(P^[k] ξ - p) + (xs (k * T) - xs (tt k + -θ'))‖ := by
          rw [htt_iter, hpk]; abel_nf
      _ ≤ ‖P^[k] ξ - p‖ + ‖xs (k * T) - xs (tt k + -θ')‖ := norm_add_le _ _
      _ ≤ C₁ * q ^ k * d + B * |k * T - (tt k + -θ')| := add_le_add (hy k) (hB _ _)
      _ = C₁ * q ^ k * d + B * |tt k - k * T - θ'| := by
          rw [abs_sub_comm]; ring_nf
      _ ≤ C₁ * q ^ k * d + B * (Cθ * d * q ^ k) := by gcongr; exact htail k
      _ = (C₁ + B * Cθ) * q ^ k * d := by ring
  -- the rate
  have hqk : q ^ k ≤ Real.exp (-(lam * t)) / q := by
    rw [le_div_iff₀ hq0, ← pow_succ]
    have h1 : t ≤ (k + 1 : ℕ) * c₀ := (hk1.le.trans (htt_le (k + 1)))
    have h2 : Real.exp (-(lam * ((k + 1 : ℕ) * c₀))) = q ^ (k + 1) := by
      rw [hlam, show -(-Real.log q / c₀ * ((k + 1 : ℕ) * c₀)) = (k + 1 : ℕ) * Real.log q by
        field_simp, Real.exp_nat_mul, Real.exp_log hq0]
    rw [← h2]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hgap : t - tt k ≤ c₀ := by
    have := htt_succ k; linarith [hτup k]
  calc ‖x t - xs (t + -θ')‖ ≤ ‖x (tt k) - xs (tt k + -θ')‖ * Real.exp (K * (t - tt k)) := hgr
    _ ≤ (C₁ + B * Cθ) * q ^ k * d * Real.exp (K * c₀) := by
        have he : Real.exp (K * (t - tt k)) ≤ Real.exp (K * c₀) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgap K.2)
        exact mul_le_mul hdev he (Real.exp_pos _).le (by positivity)
    _ ≤ (C₁ + B * Cθ) * (Real.exp (-(lam * t)) / q) * d * Real.exp (K * c₀) := by gcongr
    _ = Cx * Real.exp (-(lam * t)) * d := by rw [hCx]; field_simp
    _ ≤ max Cθ Cx * Real.exp (-(lam * t)) * d := by gcongr; exact le_max_right _ _

/-- **Andronov–Witt with asymptotic phase, uniformly along the orbit.** Under the hypotheses of
`asymptoticPhase_of_section` there are `δ > 0`, `C ≥ 0` and `λ > 0` such that every solution `x`
on `[0, ∞)` starting within `δ` of any point `x_*(σ)` of the orbit has an asymptotic phase `θ`,
`|θ| ≤ C ‖x(0) − x_*(σ)‖`, with `‖x(t) − x_*(t + σ + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(σ)‖` for all
`t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (hS : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)))) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ (σ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs σ‖ < δ →
      ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs σ‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖ := by
  obtain ⟨δ₀, C₀, lam, hδ₀, hC₀, hlam, hmain⟩ :=
    asymptoticPhase_of_section hf hfK hxs hT hper hne hS
  obtain ⟨B, hB0, hB⟩ := exists_speed_bound hfK hxs hT hper
  set E := Real.exp (K * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hT.le)
  have hE0 : 0 < E := by linarith
  set F := Real.exp (lam * T) with hF
  have hF1 : 1 ≤ F := Real.one_le_exp (mul_nonneg hlam.le hT.le)
  set C := max (C₀ * E) ((C₀ + 1 + B * C₀) * E * F) with hC
  refine ⟨δ₀ / E, C, lam, div_pos hδ₀ hE0, le_max_of_le_left (by positivity), hlam,
    fun σ x hx hx0 => ?_⟩
  set d₀ := ‖x 0 - xs σ‖ with hd₀
  have hd0 : 0 ≤ d₀ := norm_nonneg _
  -- the phase of `σ` in `[0, T)`
  set σ' := toIcoMod hT 0 σ with hσ'
  have hσ'I : σ' ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 σ
  have hshift : ∀ a, xs (a + σ) = xs (a + σ') := fun a => by
    have h := toIcoMod_add_toIcoDiv_zsmul hT 0 σ
    rw [← h, ← add_assoc]
    exact (hper.zsmul _) _
  set u := T - σ' with hu
  have hu0 : 0 < u := by have := hσ'I.2; linarith
  have huT : u ≤ T := by have := hσ'I.1; linarith
  -- up to the time `u` the solution follows `x_*(· + σ')`
  have hxs' : ∀ a b : ℝ, IsIntegralCurveOn (fun r => xs (r + σ')) (fun _ => f) (Icc a b) :=
    fun _ _ r _ => ((hxs (r + σ')).comp_add_const r σ').hasDerivWithinAt
  have hfollow : ∀ r ∈ Icc 0 u, ‖x r - xs (r + σ')‖ ≤ E * d₀ := fun r hr => by
    have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
      (hx.mono fun q hq => mem_Ici.2 hq.1) (hxs' 0 u) r hr
    have hσσ' : xs σ = xs σ' := by have := hshift 0; rwa [zero_add, zero_add] at this
    rw [dist_eq_norm, dist_eq_norm, zero_add, ← hσσ', sub_zero] at h
    rw [mul_comm] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hd0)
    exact mul_le_mul_of_nonneg_left (hr.2.trans huT) K.2
  have hxu : ‖x u - xs 0‖ ≤ E * d₀ := by
    have h := hfollow u ⟨hu0.le, le_rfl⟩
    rwa [hu, sub_add_cancel, show xs T = xs 0 by simpa using hper 0] at h
  -- from the time `u` on, the phase of `asymptoticPhase_of_section`
  set y : ℝ → Fin n → ℝ := fun r => x (r + u) with hy
  have hyI : IsIntegralCurveOn y (fun _ => f) (Ici 0) :=
    (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
      (Ici_subset_Ici.2 (by linarith))
  have hy0 : ‖y 0 - xs 0‖ < δ₀ := by
    simp only [hy, zero_add]
    calc ‖x u - xs 0‖ ≤ E * d₀ := hxu
      _ < E * (δ₀ / E) := mul_lt_mul_of_pos_left hx0 hE0
      _ = δ₀ := by field_simp
  obtain ⟨θ, hθ, hyθ⟩ := hmain y hyI hy0
  have hy0' : ‖y 0 - xs 0‖ ≤ E * d₀ := by simpa [hy] using hxu
  have hθd : |θ| ≤ C₀ * E * d₀ :=
    hθ.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy0' hC₀)
  have hθC : |θ| ≤ C * d₀ := hθd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0)
  refine ⟨θ, hθC, fun t ht => ?_⟩
  have hphase : xs (t + σ + θ) = xs (t + θ + σ') := by
    rw [show t + σ + θ = (t + θ) + σ by ring, hshift]
  rw [hphase]
  rcases le_or_gt u t with hut | htu
  · -- after the time `u`
    have h := hyθ (t - u) (by linarith)
    simp only [hy, sub_add_cancel] at h
    have hper' : xs (t - u + θ) = xs (t + θ + σ') := by
      rw [hu, show t - (T - σ') + θ = (t + θ + σ') - T by ring]
      exact hper.sub_eq _
    rw [hper'] at h
    refine h.trans ?_
    have hexp : Real.exp (-(lam * (t - u))) ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc C₀ * Real.exp (-(lam * (t - u))) * ‖y 0 - xs 0‖
        ≤ C₀ * (F * Real.exp (-(lam * t))) * (E * d₀) := by gcongr
      _ = C₀ * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ C * Real.exp (-(lam * t)) * d₀ := by
          gcongr
          rw [hC]
          refine le_max_of_le_right ?_
          have := mul_le_mul_of_nonneg_left hF1 (by positivity : (0 : ℝ) ≤ C₀ * E)
          nlinarith [mul_nonneg (mul_nonneg hB0 hC₀) (by positivity : (0 : ℝ) ≤ E * F),
            mul_nonneg hE0.le (by linarith : (0 : ℝ) ≤ F)]
  · -- before the time `u`
    have h1 := hfollow t ⟨ht, htu.le⟩
    have h2 : ‖xs (t + σ') - xs (t + θ + σ')‖ ≤ B * |θ| := by
      refine (hB _ _).trans_eq ?_
      congr 1
      rw [show t + σ' - (t + θ + σ') = -θ by ring, abs_neg]
    have hexp : 1 ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖x t - xs (t + θ + σ')‖ = ‖(x t - xs (t + σ')) + (xs (t + σ') - xs (t + θ + σ'))‖ := by
          abel_nf
      _ ≤ ‖x t - xs (t + σ')‖ + ‖xs (t + σ') - xs (t + θ + σ')‖ := norm_add_le _ _
      _ ≤ E * d₀ + B * (C₀ * E * d₀) := add_le_add h1 (h2.trans (by gcongr))
      _ = (1 + B * C₀) * E * d₀ * 1 := by ring
      _ ≤ (1 + B * C₀) * E * d₀ * (F * Real.exp (-(lam * t))) := by gcongr
      _ = (1 + B * C₀) * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ C * Real.exp (-(lam * t)) * d₀ := by
          gcongr
          rw [hC]
          refine le_max_of_le_right ?_
          have := mul_nonneg hC₀ (by positivity : (0 : ℝ) ≤ E * F)
          nlinarith

/-- **Orbital exponential stability.** Under the hypotheses of `asymptoticPhase_of_section`, the
distance to the orbit decays exponentially: every solution `x` on `[0, ∞)` with
`dist(x(0), x_*(ℝ)) < δ` satisfies `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))` for
`t ≥ 0` (`Metric.infDist` to the range of `x_*`). -/
@[tmio T, powerlib_foundation] theorem infDist_orbit_le (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (hS : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)))) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → Metric.infDist (x 0) (range xs) < δ →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  obtain ⟨δ, C, lam, hδ, hC, hlam, hph⟩ := asymptoticPhase hf hfK hxs hT hper hne hS
  refine ⟨δ, C, lam, hδ, hC, hlam, fun x hx hx0 t ht => ?_⟩
  set D := Metric.infDist (x 0) (range xs) with hD
  set c := C * Real.exp (-(lam * t)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hne' : (range xs).Nonempty := range_nonempty xs
  -- for every margin `η` a point of the orbit within `D + η`
  have key : ∀ η, 0 < η → D + η < δ → Metric.infDist (x t) (range xs) ≤ c * (D + η) := by
    intro η hη hδη
    obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff hne').1
      (show D < D + η by linarith)
    rw [dist_eq_norm] at hσ
    obtain ⟨θ, -, hθ⟩ := hph σ x hx (hσ.trans hδη)
    calc Metric.infDist (x t) (range xs) ≤ dist (x t) (xs (t + σ + θ)) :=
          Metric.infDist_le_dist_of_mem (mem_range_self _)
      _ = ‖x t - xs (t + σ + θ)‖ := dist_eq_norm _ _
      _ ≤ c * ‖x 0 - xs σ‖ := hθ t ht
      _ ≤ c * (D + η) := mul_le_mul_of_nonneg_left hσ.le hc0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η := min (ε / (c + 1)) ((δ - D) / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  have hη1 : η ≤ ε / (c + 1) := min_le_left _ _
  have hη2 : D + η < δ := by have := min_le_right (ε / (c + 1)) ((δ - D) / 2); linarith
  have h := key η hη0 hη2
  have hcη : c * η ≤ ε := by
    calc c * η ≤ (c + 1) * η := by nlinarith
      _ ≤ (c + 1) * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hη1 (by positivity)
      _ = ε := by field_simp
  linarith [mul_add c D η]

/-! ## Orbital instability -/

/-- **The orbit meets the section only at `x_*(0)` near `x_*(0)`.** For a nonconstant
`T`-periodic orbit there is `ρ > 0` such that a point `x_*(σ)` of the orbit on the hyperplane
`f(p) ⬝ (x − p) = 0`, `p = x_*(0)`, with `‖x_*(σ) − p‖ < ρ` is `p` itself (the orbit crosses the
section transversally, and returns to `p` only at the times where it closes). -/
@[tmio T, powerlib_foundation] theorem orbit_section_eq (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) :
    ∃ ρ > 0, ∀ σ, f (xs 0) ⬝ᵥ (xs σ - xs 0) = 0 → ‖xs σ - xs 0‖ < ρ → xs σ = xs 0 := by
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  -- a return to `p` is a period
  have hshift : ∀ σ', xs σ' = p → ∀ u, xs (u + σ') = xs u := fun σ' h => by
    have e := ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => univ) (K := K) (t₀ := 0)
      (f := fun u => xs (u + σ')) (g := xs) (fun _ => hfK.lipschitzOnWith)
      (fun t => ⟨(hxs (t + σ')).comp_add_const t σ', trivial⟩) (fun t => ⟨hxs t, trivial⟩)
      (by simpa using h)
    exact fun u => congrFun e u
  -- near the time `0` the orbit crosses the section only once
  have hd : HasDerivAt (fun u => v ⬝ᵥ (xs u - p)) (v ⬝ᵥ v) 0 := by
    exact (dotCLM v).hasFDerivAt.comp_hasDerivAt 0 ((hxs 0).sub_const p)
  have hloc := hd.eventually_ne (c := 0) (dotProduct_self_eq_zero.not.2 hne)
  rw [eventually_nhdsWithin_iff] at hloc
  obtain ⟨σ₀, hσ₀, hσ₀loc⟩ := Metric.eventually_nhds_iff.1 hloc
  -- away from the returns the orbit stays away from `p`
  set Z := {σ' : ℝ | σ' ∈ Icc 0 T ∧ xs σ' = p} with hZ
  set Kc := Icc 0 T ∩ {σ : ℝ | ∀ σ' ∈ Z, σ₀ ≤ |σ - σ'|} with hKc
  have hKcl : IsClosed {σ : ℝ | ∀ σ' ∈ Z, σ₀ ≤ |σ - σ'|} := by
    have e : {σ : ℝ | ∀ σ' ∈ Z, σ₀ ≤ |σ - σ'|} = ⋂ σ' ∈ Z, {σ | σ₀ ≤ |σ - σ'|} := by
      ext; simp
    rw [e]
    exact isClosed_biInter fun σ' _ => isClosed_le continuous_const (by fun_prop)
  have hKcpt : IsCompact Kc := isCompact_Icc.inter_right hKcl
  have hfar : ∃ ρ > 0, ∀ σ ∈ Kc, ρ ≤ ‖xs σ - p‖ := by
    by_cases hKne : Kc.Nonempty
    · obtain ⟨σm, hσm, hmin⟩ := hKcpt.exists_isMinOn hKne
        (continuous_norm.comp (hxc.sub continuous_const)).continuousOn
      refine ⟨‖xs σm - p‖, ?_, fun σ hσ => hmin hσ⟩
      refine norm_pos_iff.2 fun h0 => ?_
      have := hσm.2 σm ⟨hσm.1, sub_eq_zero.1 h0⟩
      rw [sub_self, abs_zero] at this
      linarith
    · exact ⟨1, one_pos, fun σ hσ => absurd ⟨σ, hσ⟩ hKne⟩
  obtain ⟨ρ, hρ, hρK⟩ := hfar
  refine ⟨ρ, hρ, fun σ hσv hσρ => ?_⟩
  obtain ⟨σ₁, hσ₁, hσσ₁⟩ := hper.exists_mem_Ico₀ hT σ
  rw [hσσ₁] at hσv hσρ ⊢
  have hσ₁K : σ₁ ∉ Kc := fun h => absurd (hρK σ₁ h) (not_le.2 hσρ)
  simp only [hKc, mem_inter_iff, Set.mem_ofPred_eq, not_and, not_forall, not_le] at hσ₁K
  obtain ⟨σ', hσ'Z, hσ'σ⟩ := hσ₁K (Ico_subset_Icc_self hσ₁)
  have he : xs σ₁ = xs (σ₁ - σ') := by
    rw [← hshift σ' hσ'Z.2 (σ₁ - σ'), sub_add_cancel]
  by_cases h0 : σ₁ - σ' = 0
  · rw [sub_eq_zero.1 h0]; exact hσ'Z.2
  · have := hσ₀loc (show dist (σ₁ - σ') 0 < σ₀ by rwa [Real.dist_eq, sub_zero]) h0
    rw [← he] at this
    exact absurd hσv this

/-- **Orbital instability.** If the monodromy of a nonconstant `T`-periodic orbit of
`ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz) has a multiplier `|μ| > 1`, the orbit is
orbitally unstable: there is `ε > 0` such that solutions starting arbitrarily close to `x_*(0)`
reach the distance `ε` from the whole orbit `x_*(ℝ)`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)))
    (h1 : 1 < ‖μ‖) :
    ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range xs) := by
  obtain ⟨τ, -, -, ⟨r, s, hr, hs, hsT, hsec, -⟩, hPp, hPD, hMv, -, -, -⟩ :=
    exists_poincareMap hf hfK hxs hT hper hne
  set P := poincareMap hfK τ with hP
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  set M := monodromy (variationalMatrix f xs) T 0 with hM
  -- the multiplier is an eigenvalue of the Poincaré Jacobian
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at h1
  have hμ1 : μ ≠ 1 := by rintro rfl; norm_num at h1
  have hμS : μ ∈ spectrum ℂ ((sectionMatrix M v).map (algebraMap ℝ ℂ)) :=
    (mem_spectrum_deflate_iff hMv (sectionVec_dotProduct hMv hne) hμ0 hμ1).2 hμ
  -- the Poincaré map is unstable at `p`
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (ε : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  obtain ⟨hE, hEp⟩ := euclid_data hPD hPp
  have hun := Map.unstable_of_eigenvalue hE.hasFDerivAt hEp hμS h1
  unfold Map.Unstable Map.LyapunovStable at hun
  push Not at hun
  obtain ⟨ε₀, hε₀, hesc⟩ := hun
  -- the Poincaré map is Lipschitz at `p`
  obtain ⟨L₀, hL₀⟩ := hPD.hasFDerivAt.isBigO_sub.bound
  obtain ⟨r₃, hr₃, hPL₀⟩ := Metric.eventually_nhds_iff.1 hL₀
  set L := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hPL : ∀ ξ, ‖ξ - p‖ < r₃ → ‖P ξ - p‖ ≤ L * ‖ξ - p‖ := fun ξ hξ => by
    have h := hPL₀ (show dist ξ p < r₃ by rwa [dist_eq_norm])
    rw [hPp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨ρS, hρS, hSig⟩ := orbit_section_eq hfK hxs hT hper hne
  -- the radii
  set ε₁ := ε₀ / (‖εS‖ + 1) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  set ε₂ := min (min ε₁ r) (min r₃ (ρS / (L + 2))) with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  have hε₂1 : ε₂ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂r : ε₂ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have hε₂r₃ : ε₂ ≤ r₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₂ρ : ε₂ ≤ ρS / (L + 2) := (min_le_right _ _).trans (min_le_right _ _)
  -- the escape set on the section, at a positive distance from the orbit
  set S := {z : Fin n → ℝ | v ⬝ᵥ (z - p) = 0 ∧ ε₂ ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ (L + 1) * ε₂} with hS
  have hScl : IsClosed S := by
    have hc1 : Continuous fun z : Fin n → ℝ => v ⬝ᵥ (z - p) :=
      (dotCLM v).continuous.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun z : Fin n → ℝ => ‖z - p‖ :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    exact (isClosed_eq hc1 continuous_const).inter
      ((isClosed_le continuous_const hc2).inter (isClosed_le hc2 continuous_const))
  have hSb : Bornology.IsBounded S :=
    (Metric.isBounded_closedBall (x := p) (r := (L + 1) * ε₂)).subset fun z hz => by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz.2.2
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  have hOcl : IsClosed (range xs) := by
    have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
    have e : range xs = xs '' Icc 0 T := by
      ext z
      constructor
      · rintro ⟨σ, rfl⟩
        obtain ⟨y, hy, hσy⟩ := hper.exists_mem_Ico₀ hT σ
        exact ⟨y, Ico_subset_Icc_self hy, hσy.symm⟩
      · rintro ⟨σ, -, rfl⟩; exact mem_range_self σ
    rw [e]
    exact (isCompact_Icc.image hxc).isClosed
  have hSpos : ∀ z ∈ S, 0 < Metric.infDist z (range xs) := fun z hz => by
    refine (hOcl.notMem_iff_infDist_pos (range_nonempty xs)).1 ?_
    rintro ⟨σ, hσ⟩
    rw [← hσ] at hz
    have hlt : ‖xs σ - p‖ < ρS := by
      calc ‖xs σ - p‖ ≤ (L + 1) * ε₂ := hz.2.2
        _ < (L + 2) * ε₂ := by nlinarith
        _ ≤ (L + 2) * (ρS / (L + 2)) := mul_le_mul_of_nonneg_left hε₂ρ (by positivity)
        _ = ρS := by field_simp
    have h0 := hSig σ hz.1 hlt
    have := hz.2.1
    rw [h0, sub_self, norm_zero] at this
    linarith
  obtain ⟨εf, hεf, hεfS⟩ : ∃ εf > 0, ∀ z ∈ S, εf ≤ Metric.infDist z (range xs) := by
    by_cases hSne : S.Nonempty
    · obtain ⟨zm, hzm, hmin⟩ := hScpt.exists_isMinOn hSne
        (Metric.continuous_infDist_pt (range xs)).continuousOn
      exact ⟨_, hSpos zm hzm, fun z hz => hmin hz⟩
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hSne⟩
  refine ⟨εf, hεf, fun δ hδ => ?_⟩
  -- an escaping orbit of the Poincaré map
  set δ' := min δ ε₂ with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ hε₂0
  obtain ⟨yE, hyE, k, hk⟩ := hesc (δ' / (‖εL‖ + 1)) (by positivity)
  set ξ := ε yE with hξ
  have hξp : ‖ξ - p‖ < δ' := by
    have e : ξ - p = ε (yE - ε.symm p) := by
      rw [map_sub, ContinuousLinearEquiv.apply_symm_apply]
    rw [e]
    calc ‖ε (yE - ε.symm p)‖ ≤ ‖εL‖ * ‖yE - ε.symm p‖ := εL.le_opNorm _
      _ ≤ (‖εL‖ + 1) * ‖yE - ε.symm p‖ := by nlinarith [norm_nonneg (yE - ε.symm p)]
      _ < δ' := by rwa [lt_div_iff₀' (by positivity)] at hyE
  have hkξ : ε₂ ≤ ‖P^[k] ξ - p‖ := by
    rw [iterate_euclidMap] at hk
    have e : ε.symm (P^[k] (ε yE)) - ε.symm p = ε.symm (P^[k] ξ - p) := by rw [map_sub]
    rw [e] at hk
    have h2 : ε₀ ≤ (‖εS‖ + 1) * ‖P^[k] ξ - p‖ :=
      hk.trans ((εS.le_opNorm _).trans (by nlinarith [norm_nonneg (P^[k] ξ - p)]))
    refine hε₂1.trans ?_
    rw [hε₁, div_le_iff₀' (by positivity)]
    exact h2
  classical
  have hex : ∃ k, ε₂ ≤ ‖P^[k] ξ - p‖ := ⟨k, hkξ⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀spec : ε₂ ≤ ‖P^[k₀] ξ - p‖ := Nat.find_spec hex
  have hk₀min : ∀ j < k₀, ‖P^[j] ξ - p‖ < ε₂ := fun j hj => not_le.1 (Nat.find_min hex hj)
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | h0
    · exfalso
      have := hk₀spec
      rw [h0, Function.iterate_zero, id] at this
      linarith [hξp.trans_le (min_le_right δ ε₂)]
    · exact h0
  -- the solution from `ξ` and its crossing at the escape
  set x := flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 ξ with hx
  have hxI : IsIntegralCurveOn x (fun _ => f) (Ici 0) := flow_solution _ _ 0 ξ
  have hx0 : x 0 = ξ := flow_start _ _ 0 ξ
  have hτnn : ∀ j < k₀, 0 ≤ τ (P^[j] (x 0)) := fun j hj => by
    rw [hx0]
    have h := (hsec _ ((hk₀min j hj).trans_le hε₂r)).1
    have := abs_lt.1 h
    linarith
  have hiter := iterate_poincareMap hfK τ hxI k₀ hτnn
  refine ⟨x, hxI, by rw [hx0]; exact hξp.trans_le (min_le_left _ _), _,
    Finset.sum_nonneg fun j hj => hτnn j (Finset.mem_range.1 hj), ?_⟩
  rw [← hiter, hx0]
  apply hεfS
  -- the escaping point lies in `S`
  set w := P^[k₀ - 1] ξ with hw
  have hwk : P^[k₀] ξ = P w := by
    rw [hw, ← Function.iterate_succ_apply' P, Nat.succ_eq_add_one, Nat.sub_add_cancel hk₀pos]
  have hwp : ‖w - p‖ < ε₂ := hk₀min (k₀ - 1) (by omega)
  refine ⟨?_, hk₀spec, ?_⟩
  · rw [hwk]; exact (hsec w (hwp.trans_le hε₂r)).2
  · rw [hwk]
    calc ‖P w - p‖ ≤ L * ‖w - p‖ := hPL w (hwp.trans_le hε₂r₃)
      _ ≤ L * ε₂ := mul_le_mul_of_nonneg_left hwp.le hL0
      _ ≤ (L + 1) * ε₂ := by nlinarith

/-! ## The Andronov–Witt theorem -/

/-- **The Poincaré map in the map semantics.** For a nonconstant `T`-periodic orbit of
`ẋ = f(x)` there is a return time `τ`, `τ(x_*(0)) = T`, whose Poincaré map, read on `ℝⁿ`, fixes
`x_*(0)`, is locally exponentially stable there when its Jacobian `sectionMatrix M f(x_*(0))` is
Schur stable, and is unstable there when the monodromy has a multiplier `|μ| > 1`. -/
@[tmio T, powerlib_foundation] theorem poincareMap_stability (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) :
    ∃ τ : (Fin n → ℝ) → ℝ, τ (xs 0) = T ∧
      euclidMap (poincareMap hfK τ) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) =
        (EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0) ∧
      (LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0))) →
        Map.LocallyExponentiallyStable (euclidMap (poincareMap hfK τ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
      ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)),
        1 < ‖μ‖ → Map.Unstable (euclidMap (poincareMap hfK τ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) := by
  obtain ⟨τ, hτp, -, -, hPp, hPD, hMv, -, -, -⟩ := exists_poincareMap hf hfK hxs hT hper hne
  obtain ⟨hE, hEp⟩ := euclid_data hPD hPp
  refine ⟨τ, hτp, hEp,
    fun hS => Map.locallyExponentiallyStable_of_schurStable hE.hasFDerivAt hEp hS,
    fun μ hμ h1 => Map.unstable_of_eigenvalue hE.hasFDerivAt hEp ?_ h1⟩
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at h1
  have hμ1 : μ ≠ 1 := by rintro rfl; norm_num at h1
  exact (mem_spectrum_deflate_iff hMv (sectionVec_dotProduct hMv hne) hμ0 hμ1).2 hμ

/-- **The Andronov–Witt theorem, deflated form.** Let `x_*` be a nonconstant `T`-periodic orbit
of `ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz) with monodromy `M` (`M f(p) = f(p)`,
`p = x_*(0)`), and let `M − f(p) wᵀ` be Schur stable for some `w` with `w ⬝ f(p) = 1` (every
nontrivial multiplier strictly inside the unit circle, `PoincareSection.schurStable_deflate_iff`).
Then the orbit is orbitally exponentially stable with asymptotic phase: there are `δ > 0`,
`C ≥ 0`, `λ > 0` such that every solution starting within `δ` of a point `x_*(σ)` satisfies
`‖x(t) − x_*(t + σ + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(σ)‖` for a phase `|θ| ≤ C ‖x(0) − x_*(σ)‖`,
and every solution starting within `δ` of the orbit satisfies
`dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))`. -/
@[tmio T, powerlib_foundation] theorem andronov_witt (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {w : Fin n → ℝ}
    (hw : w ⬝ᵥ f (xs 0) = 1)
    (hS : LTI.SchurStable (monodromy (variationalMatrix f xs) T 0 - vecMulVec (f (xs 0)) w)) :
    (∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ (σ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs σ‖ < δ →
      ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs σ‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖) ∧
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → Metric.infDist (x 0) (range xs) < δ →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  have hMv := monodromy_mulVec_velocity hf hxs hT hper
  have hS' := (schurStable_sectionMatrix_iff hMv hne hw).1.2 hS
  exact ⟨asymptoticPhase hf hfK hxs hT hper hne hS', infDist_orbit_le hf hfK hxs hT hper hne hS'⟩

/-- **The Andronov–Witt theorem, multiplier form.** If the trivial multiplier `1` of a
nonconstant `T`-periodic orbit of `ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz) is a simple
root of the characteristic polynomial of the monodromy `M` and every other multiplier lies
strictly inside the unit circle, the orbit is orbitally exponentially stable with asymptotic
phase (the two conclusions of `andronov_witt`). -/
@[tmio T, powerlib_foundation] theorem andronov_witt_of_multipliers (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (h1 : (monodromy (variationalMatrix f xs) T 0).charpoly.rootMultiplicity 1 = 1)
    (hμ : ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)),
      μ ≠ 1 → ‖μ‖ < 1) :
    (∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ (σ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs σ‖ < δ →
      ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs σ‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖) ∧
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → Metric.infDist (x 0) (range xs) < δ →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  have hMv := monodromy_mulVec_velocity hf hxs hT hper
  have hw := sectionVec_dotProduct hMv hne
  have hS := (schurStable_deflate_iff hMv hne hw).2 ⟨h1, hμ⟩
  exact andronov_witt hf hfK hxs hT hper hne hw hS

/-! ## Fields that are only locally Lipschitz -/

/-- **The localized field of a periodic orbit.** For `f` of class `C¹` and a `T`-periodic orbit
`x_*` there is a radius `R` such that the localized field `f̃ = f ∘ ψ_R`
(`LocalField.localField`) is of class `C¹` and globally Lipschitz, agrees with `f` within distance
`1` of the orbit, has `x_*` as a solution, and has the same variational matrix along `x_*`. -/
@[tmio T, powerlib_foundation] private theorem local_data (hf : ContDiff ℝ 1 f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) :
    ∃ R : ℝ, ∃ K' : NNReal, ContDiff ℝ 1 (LocalField.localField (fun _ => f) R 0) ∧
      LipschitzWith K' (LocalField.localField (fun _ => f) R 0) ∧
      (∀ (y : Fin n → ℝ) σ, ‖y - xs σ‖ ≤ 1 → ‖y‖ ≤ R) ∧
      (∀ y : Fin n → ℝ, ‖y‖ ≤ R → LocalField.localField (fun _ => f) R 0 y = f y) ∧
      (∀ t, HasDerivAt xs (LocalField.localField (fun _ => f) R 0 (xs t)) t) ∧
      variationalMatrix (LocalField.localField (fun _ => f) R 0) xs = variationalMatrix f xs := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1
    (hper.compact_of_continuous hT.ne' hxc).isBounded
  set R := B + 2 with hR
  have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => f) t) x :=
    fun _ x => (hf.differentiable one_ne_zero) x
  have hD : Continuous fun q : ℝ × (Fin n → ℝ) => fderiv ℝ ((fun _ : ℝ => f) q.1) q.2 :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_snd
  obtain ⟨K', hK'⟩ := LocalField.exists_lipschitzWith_localField hGd hD hT
    (G := fun _ => f) (fun _ => rfl) R
  have hxsR : ∀ t, ‖xs t‖ < R := fun t => by
    have := hB (xs t) (mem_range_self t); rw [hR]; linarith
  refine ⟨R, K', LocalField.contDiff_localField (G := fun _ => f) hf, hK' 0,
    fun y σ hy => ?_, fun y hy => LocalField.localField_eq hy, fun t => ?_, ?_⟩
  · have := hB (xs σ) (mem_range_self σ)
    calc ‖y‖ = ‖xs σ + (y - xs σ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖xs σ‖ + ‖y - xs σ‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  · rw [LocalField.localField_eq (hxsR t).le]; exact hxs t
  · funext t
    simp only [variationalMatrix]
    rw [LocalField.fderiv_localField_eq (G := fun _ => f) (hxsR t)]

/-- **The Andronov–Witt theorem for a `C¹` field without a global Lipschitz bound.** If the
trivial multiplier `1` of a nonconstant `T`-periodic orbit of `ẋ = f(x)` (`f` of class `C¹`) is
simple and every other multiplier lies strictly inside the unit circle, there are `δ > 0`,
`C ≥ 0`, `λ > 0` such that every point within `δ` of the orbit starts a solution on `[0, ∞)`,
every solution starting within `δ` of `x_*(σ)` has an asymptotic phase `θ`,
`|θ| ≤ C ‖x(0) − x_*(σ)‖`, with `‖x(t) − x_*(t + σ + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(σ)‖`, and every
solution starting within `δ` of the orbit satisfies
`dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))`. -/
@[tmio T, powerlib_foundation] theorem andronov_witt_local (hf : ContDiff ℝ 1 f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (h1 : (monodromy (variationalMatrix f xs) T 0).charpoly.rootMultiplicity 1 = 1)
    (hμ : ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)),
      μ ≠ 1 → ‖μ‖ < 1) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧
      (∀ ξ : Fin n → ℝ, Metric.infDist ξ (range xs) < δ →
        ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x (fun _ => f) (Ici 0)) ∧
      (∀ (σ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x (fun _ => f) (Ici 0) →
        ‖x 0 - xs σ‖ < δ → ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs σ‖ ∧
          ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖) ∧
      ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
        Metric.infDist (x 0) (range xs) < δ → ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
          C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  obtain ⟨R, K', hfl, hflK, hR1, hflf, hxsl, hvar⟩ := local_data hf hxs hT hper
  set fl := LocalField.localField (fun _ => f) R 0 with hfldef
  have hnel : fl (xs 0) ≠ 0 := by
    rwa [hflf _ (hR1 _ 0 (by simp))]
  obtain ⟨⟨δ₁, C₁, lam₁, hδ₁, hC₁, hlam₁, hph⟩, ⟨δ₂, C₂, lam₂, hδ₂, hC₂, hlam₂, hdist⟩⟩ :=
    andronov_witt_of_multipliers hfl hflK hxsl hT hper hnel (by rwa [hvar]) (by rwa [hvar])
  have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => f) t) x :=
    fun _ x => (hf.differentiable one_ne_zero) x
  have hD : Continuous fun q : ℝ × (Fin n → ℝ) => fderiv ℝ ((fun _ : ℝ => f) q.1) q.2 :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_snd
  set δ := min (min δ₁ δ₂) (1 / (C₁ + 1)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by positivity)
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδC : C₁ * δ < 1 := by
    have h := min_le_right (min δ₁ δ₂) (1 / (C₁ + 1))
    rw [← hδ] at h
    calc C₁ * δ ≤ C₁ * (1 / (C₁ + 1)) := mul_le_mul_of_nonneg_left h hC₁
      _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
  -- the solution of the localized field from a point near the orbit solves `f`
  have hflow : ∀ (σ : ℝ) (ξ : Fin n → ℝ), ‖ξ - xs σ‖ < δ →
      IsIntegralCurveOn (flow (G := fun _ => fl) (hflK.continuous.comp continuous_snd)
        (fun _ => hflK) 0 ξ) (fun _ => f) (Ici 0) := fun σ ξ hξ => by
    set y := flow (G := fun _ => fl) (hflK.continuous.comp continuous_snd) (fun _ => hflK) 0 ξ
    have hyI : IsIntegralCurveOn y (fun _ => fl) (Ici 0) := flow_solution _ _ 0 ξ
    have hy0 : y 0 = ξ := flow_start _ _ 0 ξ
    obtain ⟨θ, -, hθ⟩ := hph σ y hyI (by rw [hy0]; exact hξ.trans_le hδ1)
    refine LocalField.isIntegralCurveOn_of_localField (G := fun _ => f) hyI fun t ht => ?_
    refine hR1 _ (t + σ + θ) ?_
    refine (hθ t ht).trans ?_
    rw [hy0]
    have he : Real.exp (-(lam₁ * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mem_Ici.1 ht])
    calc C₁ * Real.exp (-(lam₁ * t)) * ‖ξ - xs σ‖ ≤ C₁ * 1 * δ := by gcongr
      _ ≤ 1 := by linarith
  -- every solution of `f` from near the orbit solves the localized field
  have hsol : ∀ (σ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      ‖x 0 - xs σ‖ < δ → IsIntegralCurveOn x (fun _ => fl) (Ici 0) := fun σ x hx hx0 => by
    set y := flow (G := fun _ => fl) (hflK.continuous.comp continuous_snd) (fun _ => hflK) 0
      (x 0)
    have hyf := hflow σ (x 0) hx0
    have hyI : IsIntegralCurveOn y (fun _ => fl) (Ici 0) := flow_solution _ _ 0 (x 0)
    have hy0 : y 0 = x 0 := flow_start _ _ 0 (x 0)
    have hxy : ∀ t, 0 ≤ t → x t = y t := fun t ht =>
      LocalField.eqOn_of_isIntegralCurveOn_Icc_of_fderiv hGd hD
        (hx.mono Icc_subset_Ici_self) (hyf.mono Icc_subset_Ici_self) hy0.symm ⟨ht, le_rfl⟩
    obtain ⟨θ, -, hθ⟩ := hph σ y hyI (by rw [hy0]; exact hx0.trans_le hδ1)
    intro t ht
    have h : HasDerivWithinAt x (f (x t)) (Ici 0) t := hx t ht
    show HasDerivWithinAt x (fl (x t)) (Ici 0) t
    rwa [← hflf (x t) ?_] at h
    rw [hxy t ht]
    refine hR1 _ (t + σ + θ) ((hθ t ht).trans ?_)
    rw [hy0]
    have he : Real.exp (-(lam₁ * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mem_Ici.1 ht])
    calc C₁ * Real.exp (-(lam₁ * t)) * ‖x 0 - xs σ‖ ≤ C₁ * 1 * δ := by gcongr
      _ ≤ 1 := by linarith
  have hnear : ∀ ξ : Fin n → ℝ, Metric.infDist ξ (range xs) < δ → ∃ σ, ‖ξ - xs σ‖ < δ :=
    fun ξ hξ => by
      obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff (range_nonempty xs)).1 hξ
      exact ⟨σ, by rwa [dist_eq_norm] at hσ⟩
  refine ⟨δ, max C₁ C₂, min lam₁ lam₂, hδ0, le_max_of_le_left hC₁, lt_min hlam₁ hlam₂,
    fun ξ hξ => ?_, fun σ x hx hx0 => ?_, fun x hx hx0 t ht => ?_⟩
  · obtain ⟨σ, hσ⟩ := hnear ξ hξ
    exact ⟨_, flow_start _ _ 0 ξ, hflow σ ξ hσ⟩
  · obtain ⟨θ, hθ, hθt⟩ := hph σ x (hsol σ x hx hx0) (hx0.trans_le hδ1)
    refine ⟨θ, hθ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
      fun t ht => (hθt t ht).trans ?_⟩
    have he : Real.exp (-(lam₁ * t)) ≤ Real.exp (-(min lam₁ lam₂ * t)) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left lam₁ lam₂])
    gcongr
    exact le_max_left _ _
  · obtain ⟨σ, hσ⟩ := hnear (x 0) hx0
    refine (hdist x (hsol σ x hx hσ) (hx0.trans_le hδ2) t ht).trans ?_
    have he : Real.exp (-(lam₂ * t)) ≤ Real.exp (-(min lam₁ lam₂ * t)) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right lam₁ lam₂])
    gcongr
    · exact Metric.infDist_nonneg
    · exact le_max_right _ _

/-- **Orbital instability for a `C¹` field without a global Lipschitz bound.** If the monodromy
of a nonconstant `T`-periodic orbit of `ẋ = f(x)` (`f` of class `C¹`) has a multiplier
`|μ| > 1`, there is `ε > 0` such that for every `δ > 0` a solution of `f` on a segment `[0, t]`
starts within `δ` of `x_*(0)` and ends at the distance `ε` or more from the orbit. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_local (hf : ContDiff ℝ 1 f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)))
    (h1 : 1 < ‖μ‖) :
    ∃ ε > 0, ∀ δ > 0, ∃ (x : ℝ → Fin n → ℝ) (t : ℝ), 0 ≤ t ∧
      IsIntegralCurveOn x (fun _ => f) (Icc 0 t) ∧ ‖x 0 - xs 0‖ < δ ∧
      ε ≤ Metric.infDist (x t) (range xs) := by
  obtain ⟨R, K', hfl, hflK, hR1, hflf, hxsl, hvar⟩ := local_data hf hxs hT hper
  set fl := LocalField.localField (fun _ => f) R 0 with hfldef
  have hnel : fl (xs 0) ≠ 0 := by
    rwa [hflf _ (hR1 _ 0 (by simp))]
  obtain ⟨ε₀, hε₀, hesc⟩ :=
    orbit_unstable hfl hflK hxsl hT hper hnel (μ := μ) (by rwa [hvar]) h1
  set ε := min ε₀ (1 / 2) with hε
  have hε0 : 0 < ε := lt_min hε₀ (by norm_num)
  have hεh : ε ≤ 1 / 2 := min_le_right _ _
  refine ⟨ε, hε0, fun δ hδ => ?_⟩
  obtain ⟨x, hxI, hx0, t, ht, hxt⟩ := hesc (min δ ε) (lt_min hδ hε0)
  set g : ℝ → ℝ := fun s => Metric.infDist (x s) (range xs) with hg
  have hxc : ContinuousOn x (Icc 0 t) := (hxI.mono Icc_subset_Ici_self).continuousOn
  have hgc : ContinuousOn g (Icc 0 t) :=
    (Metric.continuous_infDist_pt (range xs)).comp_continuousOn hxc
  have hg0 : g 0 < ε := by
    calc g 0 ≤ dist (x 0) (xs 0) := Metric.infDist_le_dist_of_mem (mem_range_self 0)
      _ = ‖x 0 - xs 0‖ := dist_eq_norm _ _
      _ < min δ ε := hx0
      _ ≤ ε := min_le_right _ _
  -- the first time at the distance `ε`
  set S := {s ∈ Icc 0 t | ε ≤ g s} with hS
  have hScl : IsClosed S := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hScpt : IsCompact S := isCompact_Icc.of_isClosed_subset hScl fun s hs => hs.1
  have htS : t ∈ S := ⟨⟨ht, le_rfl⟩, (min_le_left _ _).trans hxt⟩
  set t' := sInf S with ht'
  have ht'S : t' ∈ S := hScpt.sInf_mem ⟨t, htS⟩
  have hbefore : ∀ s ∈ Ico 0 t', g s < ε := fun s hs => by
    by_contra hcon
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans ht'S.1.2⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hScpt.bddBelow hsS) (not_le.2 hs.2)
  have ht'0 : 0 < t' := by
    rcases ht'S.1.1.eq_or_lt with h0 | h0
    · exfalso; have := ht'S.2; rw [← h0] at this; linarith
    · exact h0
  -- up to that time the solution stays within distance `1` of the orbit
  have hin : ∀ s ∈ Icc 0 t', ‖x s‖ ≤ R := by
    have hnear : ∀ s ∈ Icc 0 t, g s < 1 → ‖x s‖ ≤ R := fun s _ hs => by
      obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff (range_nonempty xs)).1 hs
      exact hR1 _ σ (by rw [dist_eq_norm] at hσ; exact hσ.le)
    intro s hs
    rcases hs.2.lt_or_eq with hlt | heq
    · exact hnear s ⟨hs.1, hlt.le.trans ht'S.1.2⟩ ((hbefore s ⟨hs.1, hlt⟩).trans_le
        (hεh.trans (by norm_num)))
    · rw [heq]
      obtain ⟨η, hη, hηx⟩ := Metric.continuousWithinAt_iff.1 (hxc t' ht'S.1) (1 / 2)
        (by norm_num)
      set s₁ := max 0 (t' - η / 2) with hs₁
      have hs₁I : s₁ ∈ Ico 0 t' := ⟨le_max_left _ _, max_lt ht'0 (by linarith)⟩
      have hs₁t : s₁ ∈ Icc 0 t := ⟨hs₁I.1, hs₁I.2.le.trans ht'S.1.2⟩
      have hd : dist (x s₁) (x t') < 1 / 2 := hηx hs₁t (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right 0 (t' - η / 2),
          hs₁I.2])
      have hgs₁ := hbefore s₁ hs₁I
      refine hnear t' ht'S.1 ?_
      calc g t' ≤ g s₁ + dist (x t') (x s₁) := Metric.infDist_le_infDist_add_dist
        _ < 1 / 2 + 1 / 2 := by rw [dist_comm]; linarith
        _ = 1 := by norm_num
  refine ⟨x, t', ht'S.1.1, ?_, hx0.trans_le (min_le_left _ _), ht'S.2⟩
  exact LocalField.isIntegralCurveOn_of_localField (G := fun _ => f)
    (hxI.mono fun s hs => mem_Ici.2 hs.1) hin

end powerlib.Periodic.AndronovWitt
